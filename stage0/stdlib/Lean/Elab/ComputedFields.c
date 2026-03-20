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
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
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
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_addZetaDeltaFVarId___redArg(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
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
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
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
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "The `[computed_field]` attribute can only be used in the with-block of an inductive"};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "elaboratingComputedFields"};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_initFn___lam__0___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 7, 196, 5, 246, 241, 200, 84)}};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "computed_field"};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(221, 37, 61, 12, 59, 99, 42, 244)}};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Marks a function as a computed field of an inductive"};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ComputedFields"};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "computedFieldAttr"};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__4_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__6_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(61, 233, 103, 138, 4, 51, 157, 24)}};
static const lean_ctor_object l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__7_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 92, 222, 191, 91, 60, 99, 108)}};
static const lean_object* l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr;
static const lean_string_object l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 538, .m_capacity = 538, .m_length = 529, .m_data = "Marks a function as a computed field of an inductive.\n\nComputed fields are specified in the with-block of an inductive type declaration. They can be used\nto allow certain values to be computed only once at the time of construction and then later be\naccessed immediately.\n\nExample:\n```\ninductive NatList where\n  | nil\n  | cons : Nat → NatList → NatList\nwith\n  @[computed_field] sum : NatList → Nat\n  | .nil => 0\n  | .cons x l => x + l.sum\n  @[computed_field] length : NatList → Nat\n  | .nil => 0\n  | .cons _ l => l.length + 1\n```\n"};
static const lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(41) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(66) << 1) | 1)),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__1_value),((lean_object*)(((size_t)(102) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(63) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__4_value),((lean_object*)(((size_t)(36) << 1) | 1))}};
static const lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "computed fields require at least two constructors"};
static const lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0 = (const lean_object*)&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0_value;
static lean_once_cell_t l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_5_);
lean_ctor_set(v___x_6_, 2, v___x_5_);
lean_ctor_set(v___x_6_, 3, v___x_4_);
lean_ctor_set(v___x_6_, 4, v___x_4_);
lean_ctor_set(v___x_6_, 5, v___x_4_);
lean_ctor_set(v___x_6_, 6, v___x_4_);
lean_ctor_set(v___x_6_, 7, v___x_4_);
lean_ctor_set(v___x_6_, 8, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
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
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_10_ = ((size_t)5ULL);
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_unsigned_to_nat(32u);
v___x_13_ = lean_mk_empty_array_with_capacity(v___x_12_);
v___x_14_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_15_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_11_);
lean_ctor_set(v___x_15_, 3, v___x_11_);
lean_ctor_set_usize(v___x_15_, 4, v___x_10_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_16_ = lean_box(1);
v___x_17_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_18_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_19_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v___x_17_);
lean_ctor_set(v___x_19_, 2, v___x_16_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v_env_25_; lean_object* v_options_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_24_ = lean_st_ref_get(v___y_22_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
lean_inc_ref(v_env_25_);
lean_dec(v___x_24_);
v_options_26_ = lean_ctor_get(v___y_21_, 2);
v___x_27_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_28_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___closed__5);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msgData_32_, v___y_33_, v___y_34_);
lean_dec(v___y_34_);
lean_dec_ref(v___y_33_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_ref_41_; lean_object* v___x_42_; lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_ref_41_ = lean_ctor_get(v___y_38_, 5);
v___x_42_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0_spec__0(v_msg_37_, v___y_38_, v___y_39_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
return v_res_56_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___lam__0___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_59_ = l_Lean_stringToMessageData(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(lean_object* v_x_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_options_70_; lean_object* v_map_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v_options_70_ = lean_ctor_get(v___y_64_, 2);
v_map_71_ = lean_ctor_get(v_options_70_, 0);
v___x_72_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___lam__0___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
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
v___x_68_ = lean_obj_once(&l_Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_, &l_Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__once, _init_l_Lean_Elab_ComputedFields_initFn___lam__0___closed__1_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_);
v___x_69_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_68_, v___y_64_, v___y_65_);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_x_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_ComputedFields_initFn___lam__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(v_x_84_, v___y_85_, v___y_86_);
lean_dec(v___y_86_);
lean_dec_ref(v___y_85_);
lean_dec(v_x_84_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___f_104_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___closed__0_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_105_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___closed__2_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_106_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___closed__3_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_107_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_108_ = 0;
v___x_109_ = lean_box(2);
v___x_110_ = l_Lean_registerTagAttribute(v___x_105_, v___x_106_, v___f_104_, v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2____boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_113_, lean_object* v_msg_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v_msg_114_, v___y_115_, v___y_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_119_, lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0(v_00_u03b1_119_, v_msg_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1(){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_128_ = ((lean_object*)(l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___closed__0));
v___x_129_ = l_Lean_addBuiltinDocString(v___x_127_, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1___boxed(lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3(){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_158_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___closed__8_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_159_ = ((lean_object*)(l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___closed__6));
v___x_160_ = l_Lean_addBuiltinDeclarationRanges(v___x_158_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3___boxed(lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
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
return v_res_191_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0(lean_object* v_msg_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v_toApplicative_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_232_; 
v___x_199_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_200_ = l_ReaderT_instMonad___redArg(v___x_199_);
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
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_769__overap_226_; lean_object* v___x_227_; 
v___x_224_ = lean_box(0);
v___x_225_ = l_instInhabitedOfMonad___redArg(v___x_223_, v___x_224_);
v___x_769__overap_226_ = lean_panic_fn(v___x_225_, v_msg_195_);
v___x_227_ = lean_apply_3(v___x_769__overap_226_, v___y_196_, v___y_197_, lean_box(0));
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
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
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
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
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
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
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
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
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
v___x_265_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_264_, v___y_255_, v___y_256_);
lean_dec(v___y_256_);
lean_dec_ref(v___y_255_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___boxed(lean_object* v_constName_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0(v_constName_300_, v___y_301_, v___y_302_);
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
lean_object* v___f_402_; lean_object* v___x_4106__overap_403_; lean_object* v___x_404_; 
v___f_402_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_4106__overap_403_ = lean_panic_fn(v___f_402_, v_msg_396_);
v___x_404_ = lean_apply_5(v___x_4106__overap_403_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, lean_box(0));
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___boxed(lean_object* v_msg_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v_msg_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_);
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
lean_inc_ref(v_a_434_);
lean_inc(v_fvarId_441_);
v___x_442_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_441_, v_a_434_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_442_) == 0)
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_500_; 
v_a_443_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_500_ == 0)
{
v___x_445_ = v___x_442_;
v_isShared_446_ = v_isSharedCheck_500_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_500_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
if (lean_obj_tag(v_a_443_) == 1)
{
uint8_t v_nondep_447_; 
v_nondep_447_ = lean_ctor_get_uint8(v_a_443_, sizeof(void*)*5);
if (v_nondep_447_ == 0)
{
lean_object* v_value_448_; lean_object* v___x_449_; 
lean_del_object(v___x_445_);
v_value_448_ = lean_ctor_get(v_a_443_, 4);
lean_inc_ref(v_value_448_);
v___x_449_ = l_Lean_Meta_getConfig___redArg(v_a_434_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_485_; 
v_a_450_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_485_ == 0)
{
v___x_452_ = v___x_449_;
v_isShared_453_ = v_isSharedCheck_485_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_449_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_485_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___y_455_; uint8_t v_trackZetaDelta_456_; lean_object* v___y_457_; lean_object* v___y_458_; lean_object* v___y_459_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_474_; lean_object* v___y_475_; uint8_t v___x_477_; 
v___x_477_ = l_Lean_LocalDecl_isImplementationDetail(v_a_443_);
lean_dec_ref(v_a_443_);
if (v___x_477_ == 0)
{
uint8_t v_zetaDelta_478_; 
v_zetaDelta_478_ = lean_ctor_get_uint8(v_a_450_, 16);
lean_dec(v_a_450_);
if (v_zetaDelta_478_ == 0)
{
uint8_t v_trackZetaDelta_479_; lean_object* v_zetaDeltaSet_480_; uint8_t v___x_481_; 
v_trackZetaDelta_479_ = lean_ctor_get_uint8(v_a_434_, sizeof(void*)*7);
v_zetaDeltaSet_480_ = lean_ctor_get(v_a_434_, 1);
v___x_481_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_441_, v_zetaDeltaSet_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_483_; 
lean_dec_ref(v_value_448_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v_e_433_);
v___x_483_ = v___x_452_;
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
else
{
lean_inc(v_fvarId_441_);
lean_del_object(v___x_452_);
lean_dec_ref(v_e_433_);
v___y_455_ = v_a_434_;
v_trackZetaDelta_456_ = v_trackZetaDelta_479_;
v___y_457_ = v_a_435_;
v___y_458_ = v_a_436_;
v___y_459_ = v_a_437_;
goto v___jp_454_;
}
}
else
{
lean_inc(v_fvarId_441_);
lean_del_object(v___x_452_);
lean_dec_ref(v_e_433_);
v___y_472_ = v_a_434_;
v___y_473_ = v_a_435_;
v___y_474_ = v_a_436_;
v___y_475_ = v_a_437_;
goto v___jp_471_;
}
}
else
{
lean_inc(v_fvarId_441_);
lean_del_object(v___x_452_);
lean_dec(v_a_450_);
lean_dec_ref(v_e_433_);
v___y_472_ = v_a_434_;
v___y_473_ = v_a_435_;
v___y_474_ = v_a_436_;
v___y_475_ = v_a_437_;
goto v___jp_471_;
}
v___jp_454_:
{
if (v_trackZetaDelta_456_ == 0)
{
lean_dec(v_fvarId_441_);
v_e_433_ = v_value_448_;
v_a_434_ = v___y_455_;
v_a_435_ = v___y_457_;
v_a_436_ = v___y_458_;
v_a_437_ = v___y_459_;
goto _start;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_441_, v___y_457_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_dec_ref(v___x_461_);
v_e_433_ = v_value_448_;
v_a_434_ = v___y_455_;
v_a_435_ = v___y_457_;
v_a_436_ = v___y_458_;
v_a_437_ = v___y_459_;
goto _start;
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_455_);
lean_dec_ref(v_value_448_);
lean_dec_ref(v_ctorTerm_432_);
v_a_463_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_461_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_461_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
v___jp_471_:
{
uint8_t v_trackZetaDelta_476_; 
v_trackZetaDelta_476_ = lean_ctor_get_uint8(v___y_472_, sizeof(void*)*7);
v___y_455_ = v___y_472_;
v_trackZetaDelta_456_ = v_trackZetaDelta_476_;
v___y_457_ = v___y_473_;
v___y_458_ = v___y_474_;
v___y_459_ = v___y_475_;
goto v___jp_454_;
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
lean_dec_ref(v_value_448_);
lean_dec_ref(v_a_443_);
lean_dec_ref(v_e_433_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
v_a_486_ = lean_ctor_get(v___x_449_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_449_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_449_);
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
else
{
lean_object* v___x_495_; 
lean_dec_ref(v_a_443_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_e_433_);
v___x_495_ = v___x_445_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_e_433_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v___x_498_; 
lean_dec(v_a_443_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 0, v_e_433_);
v___x_498_ = v___x_445_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_e_433_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v_e_433_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
v_a_501_ = lean_ctor_get(v___x_442_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_442_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_442_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_442_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_509_; lean_object* v___x_510_; 
v_mvarId_509_ = lean_ctor_get(v_e_433_, 0);
v___x_510_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_509_, v_a_435_);
if (lean_obj_tag(v___x_510_) == 0)
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_520_; 
v_a_511_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_520_ == 0)
{
v___x_513_ = v___x_510_;
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_510_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_520_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
if (lean_obj_tag(v_a_511_) == 0)
{
lean_object* v___x_516_; 
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v_e_433_);
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_e_433_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
else
{
lean_object* v_val_518_; 
lean_del_object(v___x_513_);
lean_dec_ref(v_e_433_);
v_val_518_ = lean_ctor_get(v_a_511_, 0);
lean_inc(v_val_518_);
lean_dec_ref(v_a_511_);
v_e_433_ = v_val_518_;
goto _start;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v_e_433_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
v_a_521_ = lean_ctor_get(v___x_510_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_510_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_510_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_510_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
case 3:
{
lean_object* v___x_529_; 
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v_e_433_);
return v___x_529_;
}
case 6:
{
lean_object* v___x_530_; 
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v_e_433_);
return v___x_530_;
}
case 7:
{
lean_object* v___x_531_; 
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_e_433_);
return v___x_531_;
}
case 9:
{
lean_object* v___x_532_; 
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v_e_433_);
return v___x_532_;
}
case 10:
{
lean_object* v_expr_533_; 
v_expr_533_ = lean_ctor_get(v_e_433_, 1);
lean_inc_ref(v_expr_533_);
lean_dec_ref(v_e_433_);
v_e_433_ = v_expr_533_;
goto _start;
}
default: 
{
lean_object* v___x_535_; 
lean_inc(v_a_437_);
lean_inc_ref(v_a_436_);
lean_inc(v_a_435_);
lean_inc_ref(v_a_434_);
v___x_535_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v_a_536_; uint8_t v___x_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
lean_inc_ref(v_ctorTerm_432_);
v___x_537_ = l_Lean_Expr_occurs(v_ctorTerm_432_, v_a_536_);
if (v___x_537_ == 0)
{
lean_dec(v_a_536_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
return v___x_535_;
}
else
{
uint8_t v___x_538_; lean_object* v___x_539_; 
lean_dec_ref(v___x_535_);
v___x_538_ = 0;
lean_inc(v_a_437_);
lean_inc_ref(v_a_436_);
lean_inc(v_a_435_);
lean_inc_ref(v_a_434_);
lean_inc(v_a_536_);
v___x_539_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_536_, v___x_538_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_549_; 
v_a_540_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_549_ == 0)
{
v___x_542_ = v___x_539_;
v_isShared_543_ = v_isSharedCheck_549_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_539_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_549_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
if (lean_obj_tag(v_a_540_) == 0)
{
lean_object* v___x_545_; 
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 0, v_a_536_);
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_536_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
else
{
lean_object* v_val_547_; lean_object* v___x_548_; 
lean_del_object(v___x_542_);
lean_dec(v_a_536_);
v_val_547_ = lean_ctor_get(v_a_540_, 0);
lean_inc(v_val_547_);
lean_dec_ref(v_a_540_);
v___x_548_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_432_, v_val_547_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
return v___x_548_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec(v_a_536_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
v_a_550_ = lean_ctor_get(v___x_539_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_539_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_539_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_539_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
else
{
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec_ref(v_ctorTerm_432_);
return v___x_535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(lean_object* v_ctorTerm_558_, lean_object* v_e_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
switch(lean_obj_tag(v_e_559_))
{
case 0:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec_ref(v_e_559_);
lean_dec_ref(v_ctorTerm_558_);
v___x_565_ = lean_obj_once(&l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3, &l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3_once, _init_l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___closed__3);
v___x_566_ = l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1(v___x_565_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_566_;
}
case 1:
{
lean_object* v_fvarId_567_; lean_object* v___x_568_; 
v_fvarId_567_ = lean_ctor_get(v_e_559_, 0);
lean_inc_ref(v_a_560_);
lean_inc(v_fvarId_567_);
v___x_568_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_567_, v_a_560_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_626_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_626_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_626_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_626_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
if (lean_obj_tag(v_a_569_) == 1)
{
uint8_t v_nondep_573_; 
v_nondep_573_ = lean_ctor_get_uint8(v_a_569_, sizeof(void*)*5);
if (v_nondep_573_ == 0)
{
lean_object* v_value_574_; lean_object* v___x_575_; 
lean_del_object(v___x_571_);
v_value_574_ = lean_ctor_get(v_a_569_, 4);
lean_inc_ref(v_value_574_);
v___x_575_ = l_Lean_Meta_getConfig___redArg(v_a_560_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_611_; 
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_611_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_611_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_611_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___y_581_; uint8_t v_trackZetaDelta_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_598_; lean_object* v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; uint8_t v___x_603_; 
v___x_603_ = l_Lean_LocalDecl_isImplementationDetail(v_a_569_);
lean_dec_ref(v_a_569_);
if (v___x_603_ == 0)
{
uint8_t v_zetaDelta_604_; 
v_zetaDelta_604_ = lean_ctor_get_uint8(v_a_576_, 16);
lean_dec(v_a_576_);
if (v_zetaDelta_604_ == 0)
{
uint8_t v_trackZetaDelta_605_; lean_object* v_zetaDeltaSet_606_; uint8_t v___x_607_; 
v_trackZetaDelta_605_ = lean_ctor_get_uint8(v_a_560_, sizeof(void*)*7);
v_zetaDeltaSet_606_ = lean_ctor_get(v_a_560_, 1);
v___x_607_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_fvarId_567_, v_zetaDeltaSet_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_609_; 
lean_dec_ref(v_value_574_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 0, v_e_559_);
v___x_609_ = v___x_578_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_e_559_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
else
{
lean_inc(v_fvarId_567_);
lean_del_object(v___x_578_);
lean_dec_ref(v_e_559_);
v___y_581_ = v_a_560_;
v_trackZetaDelta_582_ = v_trackZetaDelta_605_;
v___y_583_ = v_a_561_;
v___y_584_ = v_a_562_;
v___y_585_ = v_a_563_;
goto v___jp_580_;
}
}
else
{
lean_inc(v_fvarId_567_);
lean_del_object(v___x_578_);
lean_dec_ref(v_e_559_);
v___y_598_ = v_a_560_;
v___y_599_ = v_a_561_;
v___y_600_ = v_a_562_;
v___y_601_ = v_a_563_;
goto v___jp_597_;
}
}
else
{
lean_inc(v_fvarId_567_);
lean_del_object(v___x_578_);
lean_dec(v_a_576_);
lean_dec_ref(v_e_559_);
v___y_598_ = v_a_560_;
v___y_599_ = v_a_561_;
v___y_600_ = v_a_562_;
v___y_601_ = v_a_563_;
goto v___jp_597_;
}
v___jp_580_:
{
if (v_trackZetaDelta_582_ == 0)
{
lean_object* v___x_586_; 
lean_dec(v_fvarId_567_);
v___x_586_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_558_, v_value_574_, v___y_581_, v___y_583_, v___y_584_, v___y_585_);
return v___x_586_;
}
else
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_fvarId_567_, v___y_583_);
if (lean_obj_tag(v___x_587_) == 0)
{
lean_object* v___x_588_; 
lean_dec_ref(v___x_587_);
v___x_588_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_558_, v_value_574_, v___y_581_, v___y_583_, v___y_584_, v___y_585_);
return v___x_588_;
}
else
{
lean_object* v_a_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_581_);
lean_dec_ref(v_value_574_);
lean_dec_ref(v_ctorTerm_558_);
v_a_589_ = lean_ctor_get(v___x_587_, 0);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_587_);
if (v_isSharedCheck_596_ == 0)
{
v___x_591_ = v___x_587_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_a_589_);
lean_dec(v___x_587_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_a_589_);
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
}
v___jp_597_:
{
uint8_t v_trackZetaDelta_602_; 
v_trackZetaDelta_602_ = lean_ctor_get_uint8(v___y_598_, sizeof(void*)*7);
v___y_581_ = v___y_598_;
v_trackZetaDelta_582_ = v_trackZetaDelta_602_;
v___y_583_ = v___y_599_;
v___y_584_ = v___y_600_;
v___y_585_ = v___y_601_;
goto v___jp_580_;
}
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec_ref(v_value_574_);
lean_dec_ref(v_a_569_);
lean_dec_ref(v_e_559_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
v_a_612_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_575_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_575_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
else
{
lean_object* v___x_621_; 
lean_dec_ref(v_a_569_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_e_559_);
v___x_621_ = v___x_571_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_e_559_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
else
{
lean_object* v___x_624_; 
lean_dec(v_a_569_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v_e_559_);
v___x_624_ = v___x_571_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_e_559_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
else
{
lean_object* v_a_627_; lean_object* v___x_629_; uint8_t v_isShared_630_; uint8_t v_isSharedCheck_634_; 
lean_dec_ref(v_e_559_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
v_a_627_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_634_ == 0)
{
v___x_629_ = v___x_568_;
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
else
{
lean_inc(v_a_627_);
lean_dec(v___x_568_);
v___x_629_ = lean_box(0);
v_isShared_630_ = v_isSharedCheck_634_;
goto v_resetjp_628_;
}
v_resetjp_628_:
{
lean_object* v___x_632_; 
if (v_isShared_630_ == 0)
{
v___x_632_ = v___x_629_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_627_);
v___x_632_ = v_reuseFailAlloc_633_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
return v___x_632_;
}
}
}
}
case 2:
{
lean_object* v_mvarId_635_; lean_object* v___x_636_; 
v_mvarId_635_ = lean_ctor_get(v_e_559_, 0);
v___x_636_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_635_, v_a_561_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_646_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_646_ == 0)
{
v___x_639_ = v___x_636_;
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_636_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_646_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
if (lean_obj_tag(v_a_637_) == 0)
{
lean_object* v___x_642_; 
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
if (v_isShared_640_ == 0)
{
lean_ctor_set(v___x_639_, 0, v_e_559_);
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_e_559_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
else
{
lean_object* v_val_644_; lean_object* v___x_645_; 
lean_del_object(v___x_639_);
lean_dec_ref(v_e_559_);
v_val_644_ = lean_ctor_get(v_a_637_, 0);
lean_inc(v_val_644_);
lean_dec_ref(v_a_637_);
v___x_645_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_558_, v_val_644_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_645_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v_e_559_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
v_a_647_ = lean_ctor_get(v___x_636_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_636_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_636_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
case 3:
{
lean_object* v___x_655_; 
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_e_559_);
return v___x_655_;
}
case 6:
{
lean_object* v___x_656_; 
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_e_559_);
return v___x_656_;
}
case 7:
{
lean_object* v___x_657_; 
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_e_559_);
return v___x_657_;
}
case 9:
{
lean_object* v___x_658_; 
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
v___x_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_658_, 0, v_e_559_);
return v___x_658_;
}
case 10:
{
lean_object* v_expr_659_; lean_object* v___x_660_; 
v_expr_659_ = lean_ctor_get(v_e_559_, 1);
lean_inc_ref(v_expr_659_);
lean_dec_ref(v_e_559_);
v___x_660_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_558_, v_expr_659_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_660_;
}
default: 
{
lean_object* v___x_661_; 
lean_inc(v_a_563_);
lean_inc_ref(v_a_562_);
lean_inc(v_a_561_);
lean_inc_ref(v_a_560_);
v___x_661_ = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfCore_go(v_e_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; uint8_t v___x_663_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_inc_ref(v_ctorTerm_558_);
v___x_663_ = l_Lean_Expr_occurs(v_ctorTerm_558_, v_a_662_);
if (v___x_663_ == 0)
{
lean_dec(v_a_662_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
return v___x_661_;
}
else
{
uint8_t v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v___x_661_);
v___x_664_ = 0;
lean_inc(v_a_563_);
lean_inc_ref(v_a_562_);
lean_inc(v_a_561_);
lean_inc_ref(v_a_560_);
lean_inc(v_a_662_);
v___x_665_ = l_Lean_Meta_unfoldDefinition_x3f(v_a_662_, v___x_664_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
if (lean_obj_tag(v___x_665_) == 0)
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_675_; 
v_a_666_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_675_ == 0)
{
v___x_668_ = v___x_665_;
v_isShared_669_ = v_isSharedCheck_675_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_665_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_675_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
if (lean_obj_tag(v_a_666_) == 0)
{
lean_object* v___x_671_; 
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v_a_662_);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_662_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
lean_object* v_val_673_; lean_object* v___x_674_; 
lean_del_object(v___x_668_);
lean_dec(v_a_662_);
v_val_673_ = lean_ctor_get(v_a_666_, 0);
lean_inc(v_val_673_);
lean_dec_ref(v_a_666_);
v___x_674_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_558_, v_val_673_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
return v___x_674_;
}
}
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec(v_a_662_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
v_a_676_ = lean_ctor_get(v___x_665_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_665_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_665_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_665_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
else
{
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
lean_dec_ref(v_ctorTerm_558_);
return v___x_661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(lean_object* v_ctorTerm_684_, lean_object* v_e_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_684_, v_e_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0___boxed(lean_object* v_ctorTerm_692_, lean_object* v_e_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_, lean_object* v_a_697_, lean_object* v_a_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_692_, v_e_693_, v_a_694_, v_a_695_, v_a_696_, v_a_697_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_700_, lean_object* v_e_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_700_, v_e_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_708_, lean_object* v_e_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_708_, v_e_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
return v_res_715_;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = ((lean_object*)(l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__0));
v___x_718_ = l_Lean_stringToMessageData(v___x_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(lean_object* v_constName_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v___x_725_; lean_object* v_env_726_; lean_object* v___x_727_; 
v___x_725_ = lean_st_ref_get(v___y_723_);
v_env_726_ = lean_ctor_get(v___x_725_, 0);
lean_inc_ref(v_env_726_);
lean_dec(v___x_725_);
lean_inc(v_constName_719_);
v___x_727_ = l_Lean_isInductiveCore_x3f(v_env_726_, v_constName_719_);
if (lean_obj_tag(v___x_727_) == 0)
{
lean_object* v___x_728_; uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_728_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_729_ = 0;
v___x_730_ = l_Lean_MessageData_ofConstName(v_constName_719_, v___x_729_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_728_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = lean_obj_once(&l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1, &l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1_once, _init_l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___closed__1);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_733_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
return v___x_734_;
}
else
{
lean_object* v_val_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_constName_719_);
v_val_735_ = lean_ctor_get(v___x_727_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_727_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_727_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_val_735_);
lean_dec(v___x_727_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 0);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_val_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3___boxed(lean_object* v_constName_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_constName_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec_ref(v___y_744_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(lean_object* v_msg_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v_toApplicative_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_821_; 
v___x_758_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_759_ = l_ReaderT_instMonad___redArg(v___x_758_);
v_toApplicative_760_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v___x_759_, 1);
lean_dec(v_unused_822_);
v___x_762_ = v___x_759_;
v_isShared_763_ = v_isSharedCheck_821_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_toApplicative_760_);
lean_dec(v___x_759_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_821_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v_toFunctor_764_; lean_object* v_toSeq_765_; lean_object* v_toSeqLeft_766_; lean_object* v_toSeqRight_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_819_; 
v_toFunctor_764_ = lean_ctor_get(v_toApplicative_760_, 0);
v_toSeq_765_ = lean_ctor_get(v_toApplicative_760_, 2);
v_toSeqLeft_766_ = lean_ctor_get(v_toApplicative_760_, 3);
v_toSeqRight_767_ = lean_ctor_get(v_toApplicative_760_, 4);
v_isSharedCheck_819_ = !lean_is_exclusive(v_toApplicative_760_);
if (v_isSharedCheck_819_ == 0)
{
lean_object* v_unused_820_; 
v_unused_820_ = lean_ctor_get(v_toApplicative_760_, 1);
lean_dec(v_unused_820_);
v___x_769_ = v_toApplicative_760_;
v_isShared_770_ = v_isSharedCheck_819_;
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
v_isShared_770_ = v_isSharedCheck_819_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___f_778_; lean_object* v___x_780_; 
v___f_771_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_772_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
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
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_818_, 1, v___f_771_);
lean_ctor_set(v_reuseFailAlloc_818_, 2, v___f_778_);
lean_ctor_set(v_reuseFailAlloc_818_, 3, v___f_777_);
lean_ctor_set(v_reuseFailAlloc_818_, 4, v___f_776_);
v___x_780_ = v_reuseFailAlloc_818_;
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
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_780_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___f_772_);
v___x_782_ = v_reuseFailAlloc_817_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v_toApplicative_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_815_; 
v___x_783_ = l_ReaderT_instMonad___redArg(v___x_782_);
v_toApplicative_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_815_ == 0)
{
lean_object* v_unused_816_; 
v_unused_816_ = lean_ctor_get(v___x_783_, 1);
lean_dec(v_unused_816_);
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_815_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_toApplicative_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_815_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_toFunctor_788_; lean_object* v_toSeq_789_; lean_object* v_toSeqLeft_790_; lean_object* v_toSeqRight_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_813_; 
v_toFunctor_788_ = lean_ctor_get(v_toApplicative_784_, 0);
v_toSeq_789_ = lean_ctor_get(v_toApplicative_784_, 2);
v_toSeqLeft_790_ = lean_ctor_get(v_toApplicative_784_, 3);
v_toSeqRight_791_ = lean_ctor_get(v_toApplicative_784_, 4);
v_isSharedCheck_813_ = !lean_is_exclusive(v_toApplicative_784_);
if (v_isSharedCheck_813_ == 0)
{
lean_object* v_unused_814_; 
v_unused_814_ = lean_ctor_get(v_toApplicative_784_, 1);
lean_dec(v_unused_814_);
v___x_793_ = v_toApplicative_784_;
v_isShared_794_ = v_isSharedCheck_813_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_toSeqRight_791_);
lean_inc(v_toSeqLeft_790_);
lean_inc(v_toSeq_789_);
lean_inc(v_toFunctor_788_);
lean_dec(v_toApplicative_784_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_813_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___x_799_; lean_object* v___f_800_; lean_object* v___f_801_; lean_object* v___f_802_; lean_object* v___x_804_; 
v___f_795_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_796_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_788_);
v___f_797_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_797_, 0, v_toFunctor_788_);
v___f_798_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_798_, 0, v_toFunctor_788_);
v___x_799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_799_, 0, v___f_797_);
lean_ctor_set(v___x_799_, 1, v___f_798_);
v___f_800_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_800_, 0, v_toSeqRight_791_);
v___f_801_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_801_, 0, v_toSeqLeft_790_);
v___f_802_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_802_, 0, v_toSeq_789_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 4, v___f_800_);
lean_ctor_set(v___x_793_, 3, v___f_801_);
lean_ctor_set(v___x_793_, 2, v___f_802_);
lean_ctor_set(v___x_793_, 1, v___f_795_);
lean_ctor_set(v___x_793_, 0, v___x_799_);
v___x_804_ = v___x_793_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___f_795_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v___f_802_);
lean_ctor_set(v_reuseFailAlloc_812_, 3, v___f_801_);
lean_ctor_set(v_reuseFailAlloc_812_, 4, v___f_800_);
v___x_804_ = v_reuseFailAlloc_812_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
lean_object* v___x_806_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 1, v___f_796_);
lean_ctor_set(v___x_786_, 0, v___x_804_);
v___x_806_ = v___x_786_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v___x_804_);
lean_ctor_set(v_reuseFailAlloc_811_, 1, v___f_796_);
v___x_806_ = v_reuseFailAlloc_811_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_4096__overap_809_; lean_object* v___x_810_; 
v___x_807_ = lean_box(0);
v___x_808_ = l_instInhabitedOfMonad___redArg(v___x_806_, v___x_807_);
v___x_4096__overap_809_ = lean_panic_fn(v___x_808_, v_msg_752_);
v___x_810_ = lean_apply_5(v___x_4096__overap_809_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, lean_box(0));
return v___x_810_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___boxed(lean_object* v_msg_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v_msg_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(lean_object* v_constName_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v___x_844_; lean_object* v_env_845_; uint8_t v___x_846_; lean_object* v___x_847_; 
v___x_844_ = lean_st_ref_get(v___y_834_);
v_env_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_ref(v_env_845_);
lean_dec(v___x_844_);
v___x_846_ = 0;
lean_inc(v_constName_830_);
v___x_847_ = l_Lean_Environment_findAsync_x3f(v_env_845_, v_constName_830_, v___x_846_);
if (lean_obj_tag(v___x_847_) == 1)
{
lean_object* v_val_848_; uint8_t v_kind_849_; 
v_val_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_val_848_);
lean_dec_ref(v___x_847_);
v_kind_849_ = lean_ctor_get_uint8(v_val_848_, sizeof(void*)*3);
if (v_kind_849_ == 6)
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_848_);
if (lean_obj_tag(v___x_850_) == 6)
{
lean_object* v_val_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v_constName_830_);
v_val_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_val_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set_tag(v___x_853_, 0);
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_val_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; 
lean_dec_ref(v___x_850_);
v___x_859_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__7);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
v___x_860_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4(v___x_859_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_869_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_869_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_869_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
if (lean_obj_tag(v_a_861_) == 0)
{
lean_del_object(v___x_863_);
goto v___jp_836_;
}
else
{
lean_object* v_val_865_; lean_object* v___x_867_; 
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v_constName_830_);
v_val_865_ = lean_ctor_get(v_a_861_, 0);
lean_inc(v_val_865_);
lean_dec_ref(v_a_861_);
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_val_865_);
v___x_867_ = v___x_863_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_val_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v_constName_830_);
v_a_870_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_860_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_860_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
else
{
lean_dec(v_val_848_);
goto v___jp_836_;
}
}
else
{
lean_dec(v___x_847_);
goto v___jp_836_;
}
v___jp_836_:
{
lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_837_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_838_ = 0;
v___x_839_ = l_Lean_MessageData_ofConstName(v_constName_830_, v___x_838_);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_837_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__3);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_842_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__0));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_889_ = ((lean_object*)(l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__2));
v___x_890_ = l_Lean_stringToMessageData(v___x_889_);
return v___x_890_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4(void){
_start:
{
lean_object* v___x_891_; lean_object* v_dummy_892_; 
v___x_891_ = lean_box(0);
v_dummy_892_ = l_Lean_Expr_sort___override(v___x_891_);
return v_dummy_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue(lean_object* v_computedField_893_, lean_object* v_ctorTerm_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_900_; lean_object* v_ctorName_901_; lean_object* v_val_903_; lean_object* v___y_904_; lean_object* v___y_905_; lean_object* v___y_906_; lean_object* v___y_907_; lean_object* v___x_919_; 
v___x_900_ = l_Lean_Expr_getAppFn(v_ctorTerm_894_);
v_ctorName_901_ = l_Lean_Expr_constName_x21(v___x_900_);
lean_dec_ref(v___x_900_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
lean_inc(v_ctorName_901_);
v___x_919_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_ctorName_901_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v_induct_921_; lean_object* v___x_922_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_919_);
v_induct_921_ = lean_ctor_get(v_a_920_, 1);
lean_inc(v_induct_921_);
lean_dec(v_a_920_);
v___x_922_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_induct_921_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v_numParams_924_; lean_object* v_numIndices_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v___x_922_);
v_numParams_924_ = lean_ctor_get(v_a_923_, 1);
lean_inc(v_numParams_924_);
v_numIndices_925_ = lean_ctor_get(v_a_923_, 2);
lean_inc(v_numIndices_925_);
lean_dec(v_a_923_);
v___x_926_ = lean_nat_add(v_numParams_924_, v_numIndices_925_);
lean_dec(v_numIndices_925_);
lean_dec(v_numParams_924_);
v___x_927_ = lean_box(0);
v___x_928_ = lean_mk_array(v___x_926_, v___x_927_);
lean_inc_ref(v_ctorTerm_894_);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v_ctorTerm_894_);
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_mk_empty_array_with_capacity(v___x_930_);
v___x_932_ = lean_array_push(v___x_931_, v___x_929_);
v___x_933_ = l_Array_append___redArg(v___x_928_, v___x_932_);
lean_dec_ref(v___x_932_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
lean_inc(v_computedField_893_);
v___x_934_ = l_Lean_Meta_mkAppOptM(v_computedField_893_, v___x_933_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_936_; lean_object* v_env_937_; lean_object* v___x_938_; lean_object* v_toEnvExtension_939_; lean_object* v_asyncMode_940_; lean_object* v___x_941_; uint8_t v___x_942_; lean_object* v___x_943_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref(v___x_934_);
v___x_936_ = lean_st_ref_get(v_a_898_);
v_env_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_env_937_);
lean_dec(v___x_936_);
v___x_938_ = l_Lean_Elab_WF_eqnInfoExt;
v_toEnvExtension_939_ = lean_ctor_get(v___x_938_, 0);
lean_inc_ref(v_toEnvExtension_939_);
v_asyncMode_940_ = lean_ctor_get(v_toEnvExtension_939_, 2);
lean_inc(v_asyncMode_940_);
lean_dec_ref(v_toEnvExtension_939_);
v___x_941_ = l_Lean_Elab_WF_instInhabitedEqnInfo_default;
v___x_942_ = 0;
lean_inc(v_computedField_893_);
v___x_943_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_941_, v___x_938_, v_env_937_, v_computedField_893_, v_asyncMode_940_, v___x_942_);
lean_dec(v_asyncMode_940_);
if (lean_obj_tag(v___x_943_) == 1)
{
lean_object* v_val_944_; lean_object* v_levelParams_945_; lean_object* v_value_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_dummy_950_; lean_object* v_nargs_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_val_944_ = lean_ctor_get(v___x_943_, 0);
lean_inc(v_val_944_);
lean_dec_ref(v___x_943_);
v_levelParams_945_ = lean_ctor_get(v_val_944_, 1);
lean_inc(v_levelParams_945_);
v_value_946_ = lean_ctor_get(v_val_944_, 3);
lean_inc_ref(v_value_946_);
lean_dec(v_val_944_);
v___x_947_ = l_Lean_Expr_getAppFn(v_a_935_);
v___x_948_ = l_Lean_Expr_constLevels_x21(v___x_947_);
lean_dec_ref(v___x_947_);
v___x_949_ = l_Lean_Expr_instantiateLevelParams(v_value_946_, v_levelParams_945_, v___x_948_);
lean_dec_ref(v_value_946_);
v_dummy_950_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
v_nargs_951_ = l_Lean_Expr_getAppNumArgs(v_a_935_);
lean_inc(v_nargs_951_);
v___x_952_ = lean_mk_array(v_nargs_951_, v_dummy_950_);
v___x_953_ = lean_nat_sub(v_nargs_951_, v___x_930_);
lean_dec(v_nargs_951_);
v___x_954_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_935_, v___x_952_, v___x_953_);
v___x_955_ = l_Lean_mkAppN(v___x_949_, v___x_954_);
lean_dec_ref(v___x_954_);
v_val_903_ = v___x_955_;
v___y_904_ = v_a_895_;
v___y_905_ = v_a_896_;
v___y_906_ = v_a_897_;
v___y_907_ = v_a_898_;
goto v___jp_902_;
}
else
{
lean_object* v___x_956_; 
lean_dec(v___x_943_);
lean_inc(v_a_898_);
lean_inc_ref(v_a_897_);
lean_inc(v_a_896_);
lean_inc_ref(v_a_895_);
v___x_956_ = l_Lean_Meta_unfoldDefinition(v_a_935_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_a_957_; 
v_a_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_a_957_);
lean_dec_ref(v___x_956_);
v_val_903_ = v_a_957_;
v___y_904_ = v_a_895_;
v___y_905_ = v_a_896_;
v___y_906_ = v_a_897_;
v___y_907_ = v_a_898_;
goto v___jp_902_;
}
else
{
lean_dec(v_ctorName_901_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec_ref(v_ctorTerm_894_);
lean_dec(v_computedField_893_);
return v___x_956_;
}
}
}
else
{
lean_dec(v_ctorName_901_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec_ref(v_ctorTerm_894_);
lean_dec(v_computedField_893_);
return v___x_934_;
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_ctorName_901_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec_ref(v_ctorTerm_894_);
lean_dec(v_computedField_893_);
v_a_958_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_922_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_922_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v_ctorName_901_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec_ref(v_ctorTerm_894_);
lean_dec(v_computedField_893_);
v_a_966_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_919_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_919_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
v___jp_902_:
{
lean_object* v___x_908_; 
lean_inc(v___y_907_);
lean_inc_ref(v___y_906_);
lean_inc(v___y_905_);
lean_inc_ref(v___y_904_);
lean_inc_ref(v_ctorTerm_894_);
v___x_908_ = l_Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0(v_ctorTerm_894_, v_val_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; uint8_t v___x_910_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
v___x_910_ = l_Lean_Expr_occurs(v_ctorTerm_894_, v_a_909_);
lean_dec(v_a_909_);
if (v___x_910_ == 0)
{
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v_ctorName_901_);
lean_dec(v_computedField_893_);
return v___x_908_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref(v___x_908_);
v___x_911_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
v___x_912_ = l_Lean_MessageData_ofName(v_computedField_893_);
v___x_913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__3);
v___x_915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_913_);
lean_ctor_set(v___x_915_, 1, v___x_914_);
v___x_916_ = l_Lean_MessageData_ofName(v_ctorName_901_);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_917_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
return v___x_918_;
}
}
else
{
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v_ctorName_901_);
lean_dec_ref(v_ctorTerm_894_);
lean_dec(v_computedField_893_);
return v___x_908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_getComputedFieldValue___boxed(lean_object* v_computedField_974_, lean_object* v_ctorTerm_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_computedField_974_, v_ctorTerm_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(lean_object* v_00_u03b1_982_, lean_object* v_msg_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v_msg_983_, v___y_984_, v___y_985_, v___y_986_, v___y_987_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___boxed(lean_object* v_00_u03b1_990_, lean_object* v_msg_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1(v_00_u03b1_990_, v_msg_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v___y_992_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(lean_object* v_mvarId_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; 
v___x_1004_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___redArg(v_mvarId_998_, v___y_1000_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4___boxed(lean_object* v_mvarId_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_getExprMVarAssignment_x3f___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__4(v_mvarId_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v_mvarId_1005_);
return v_res_1011_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_1012_, lean_object* v_k_1013_, lean_object* v_t_1014_){
_start:
{
uint8_t v___x_1015_; 
v___x_1015_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___redArg(v_k_1013_, v_t_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_1016_, lean_object* v_k_1017_, lean_object* v_t_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__3(v_00_u03b2_1016_, v_k_1017_, v_t_1018_);
lean_dec(v_t_1018_);
lean_dec(v_k_1017_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(lean_object* v_a_1021_, lean_object* v_as_1022_, size_t v_i_1023_, size_t v_stop_1024_){
_start:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_usize_dec_eq(v_i_1023_, v_stop_1024_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1026_ = lean_array_uget_borrowed(v_as_1022_, v_i_1023_);
v___x_1027_ = l_Lean_Expr_fvarId_x21(v___x_1026_);
v___x_1028_ = l_Lean_Expr_containsFVar(v_a_1021_, v___x_1027_);
lean_dec(v___x_1027_);
if (v___x_1028_ == 0)
{
size_t v___x_1029_; size_t v___x_1030_; 
v___x_1029_ = ((size_t)1ULL);
v___x_1030_ = lean_usize_add(v_i_1023_, v___x_1029_);
v_i_1023_ = v___x_1030_;
goto _start;
}
else
{
return v___x_1028_;
}
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = 0;
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0___boxed(lean_object* v_a_1033_, lean_object* v_as_1034_, lean_object* v_i_1035_, lean_object* v_stop_1036_){
_start:
{
size_t v_i_boxed_1037_; size_t v_stop_boxed_1038_; uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_i_boxed_1037_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_stop_boxed_1038_ = lean_unbox_usize(v_stop_1036_);
lean_dec(v_stop_1036_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1033_, v_as_1034_, v_i_boxed_1037_, v_stop_boxed_1038_);
lean_dec_ref(v_as_1034_);
lean_dec_ref(v_a_1033_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(lean_object* v_msg_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_ref_1047_; lean_object* v___x_1048_; lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
v_ref_1047_ = lean_ctor_get(v___y_1044_, 5);
v___x_1048_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v_msg_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_);
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1051_ = v___x_1048_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1048_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_inc(v_ref_1047_);
v___x_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_ref_1047_);
lean_ctor_set(v___x_1053_, 1, v_a_1049_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set_tag(v___x_1051_, 1);
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg___boxed(lean_object* v_msg_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
return v_res_1064_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__0));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__2));
v___x_1070_ = l_Lean_stringToMessageData(v___x_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(lean_object* v_indices_1071_, lean_object* v_val_1072_, lean_object* v_as_1073_, size_t v_sz_1074_, size_t v_i_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_a_1084_; uint8_t v___x_1088_; 
v___x_1088_ = lean_usize_dec_lt(v_i_1075_, v_sz_1074_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; 
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v_b_1076_);
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1091_; 
v_a_1090_ = lean_array_uget_borrowed(v_as_1073_, v_i_1075_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v_a_1090_);
v___x_1091_ = lean_infer_type(v_a_1090_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v_a_1092_; lean_object* v___x_1093_; lean_object* v___y_1095_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = lean_box(0);
v___x_1114_ = l_Lean_Expr_fvarId_x21(v_val_1072_);
v___x_1115_ = l_Lean_Expr_containsFVar(v_a_1092_, v___x_1114_);
lean_dec(v___x_1114_);
if (v___x_1115_ == 0)
{
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
v___y_1095_ = v___y_1077_;
v___y_1096_ = v___y_1078_;
v___y_1097_ = v___y_1079_;
v___y_1098_ = v___y_1080_;
v___y_1099_ = v___y_1081_;
goto v___jp_1094_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1116_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1090_);
v___x_1117_ = l_Lean_MessageData_ofExpr(v_a_1090_);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__3);
v___x_1120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1118_);
lean_ctor_set(v___x_1120_, 1, v___x_1119_);
lean_inc(v_a_1092_);
v___x_1121_ = l_Lean_indentExpr(v_a_1092_);
v___x_1122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1120_);
lean_ctor_set(v___x_1122_, 1, v___x_1121_);
v___x_1123_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1122_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_dec_ref(v___x_1123_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
v___y_1095_ = v___y_1077_;
v___y_1096_ = v___y_1078_;
v___y_1097_ = v___y_1079_;
v___y_1098_ = v___y_1080_;
v___y_1099_ = v___y_1081_;
goto v___jp_1094_;
}
else
{
lean_dec(v_a_1092_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v___x_1123_;
}
}
v___jp_1094_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_array_get_size(v_indices_1071_);
v___x_1102_ = lean_nat_dec_lt(v___x_1100_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v_a_1092_);
v_a_1084_ = v___x_1093_;
goto v___jp_1083_;
}
else
{
if (v___x_1102_ == 0)
{
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v_a_1092_);
v_a_1084_ = v___x_1093_;
goto v___jp_1083_;
}
else
{
size_t v___x_1103_; size_t v___x_1104_; uint8_t v___x_1105_; 
v___x_1103_ = ((size_t)0ULL);
v___x_1104_ = lean_usize_of_nat(v___x_1101_);
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__0(v_a_1092_, v_indices_1071_, v___x_1103_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v_a_1092_);
v_a_1084_ = v___x_1093_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1106_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__1);
lean_inc(v_a_1090_);
v___x_1107_ = l_Lean_MessageData_ofExpr(v_a_1090_);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1106_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
v___x_1109_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___closed__1);
v___x_1110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1108_);
lean_ctor_set(v___x_1110_, 1, v___x_1109_);
v___x_1111_ = l_Lean_indentExpr(v_a_1092_);
v___x_1112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1110_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1112_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref(v___x_1113_);
v_a_1084_ = v___x_1093_;
goto v___jp_1083_;
}
else
{
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
return v___x_1113_;
}
}
}
}
}
}
else
{
lean_object* v_a_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1131_; 
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
v_a_1124_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1126_ = v___x_1091_;
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_a_1124_);
lean_dec(v___x_1091_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1131_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v___x_1129_; 
if (v_isShared_1127_ == 0)
{
v___x_1129_ = v___x_1126_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1124_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
}
v___jp_1083_:
{
size_t v___x_1085_; size_t v___x_1086_; 
v___x_1085_ = ((size_t)1ULL);
v___x_1086_ = lean_usize_add(v_i_1075_, v___x_1085_);
v_i_1075_ = v___x_1086_;
v_b_1076_ = v_a_1084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2___boxed(lean_object* v_indices_1132_, lean_object* v_val_1133_, lean_object* v_as_1134_, lean_object* v_sz_1135_, lean_object* v_i_1136_, lean_object* v_b_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
size_t v_sz_boxed_1144_; size_t v_i_boxed_1145_; lean_object* v_res_1146_; 
v_sz_boxed_1144_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1145_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1132_, v_val_1133_, v_as_1134_, v_sz_boxed_1144_, v_i_boxed_1145_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec_ref(v___y_1138_);
lean_dec_ref(v_as_1134_);
lean_dec_ref(v_val_1133_);
lean_dec_ref(v_indices_1132_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields(lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
lean_object* v_compFieldVars_1153_; lean_object* v_indices_1154_; lean_object* v_val_1155_; lean_object* v___x_1156_; size_t v_sz_1157_; size_t v___x_1158_; lean_object* v___x_1159_; 
v_compFieldVars_1153_ = lean_ctor_get(v_a_1147_, 4);
v_indices_1154_ = lean_ctor_get(v_a_1147_, 5);
v_val_1155_ = lean_ctor_get(v_a_1147_, 6);
v___x_1156_ = lean_box(0);
v_sz_1157_ = lean_array_size(v_compFieldVars_1153_);
v___x_1158_ = ((size_t)0ULL);
v___x_1159_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__2(v_indices_1154_, v_val_1155_, v_compFieldVars_1153_, v_sz_1157_, v___x_1158_, v___x_1156_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; 
v_unused_1167_ = lean_ctor_get(v___x_1159_, 0);
lean_dec(v_unused_1167_);
v___x_1161_ = v___x_1159_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_dec(v___x_1159_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
lean_ctor_set(v___x_1161_, 0, v___x_1156_);
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1156_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
else
{
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_validateComputedFields___boxed(lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_Elab_ComputedFields_validateComputedFields(v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec_ref(v_a_1168_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(lean_object* v_00_u03b1_1175_, lean_object* v_msg_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v_msg_1176_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_msg_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1(v_00_u03b1_1184_, v_msg_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec_ref(v___y_1186_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(lean_object* v_k_1193_, lean_object* v___y_1194_, lean_object* v_b_1195_, lean_object* v_c_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = lean_apply_8(v_k_1193_, v_b_1195_, v_c_1196_, v___y_1194_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, lean_box(0));
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1203_, lean_object* v___y_1204_, lean_object* v_b_1205_, lean_object* v_c_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1203_, v___y_1204_, v_b_1205_, v_c_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1213_, lean_object* v_k_1214_, uint8_t v_cleanupAnnotations_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___f_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1222_, 0, v_k_1214_);
lean_closure_set(v___f_1222_, 1, v___y_1216_);
v___x_1223_ = 0;
v___x_1224_ = lean_box(0);
v___x_1225_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_1223_, v___x_1224_, v_type_1213_, v___f_1222_, v_cleanupAnnotations_1215_, v___x_1223_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
if (lean_obj_tag(v___x_1225_) == 0)
{
return v___x_1225_;
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1225_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1225_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___boxed(lean_object* v_type_1234_, lean_object* v_k_1235_, lean_object* v_cleanupAnnotations_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1243_; lean_object* v_res_1244_; 
v_cleanupAnnotations_boxed_1243_ = lean_unbox(v_cleanupAnnotations_1236_);
v_res_1244_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1234_, v_k_1235_, v_cleanupAnnotations_boxed_1243_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(lean_object* v_00_u03b1_1245_, lean_object* v_type_1246_, lean_object* v_k_1247_, uint8_t v_cleanupAnnotations_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_type_1246_, v_k_1247_, v_cleanupAnnotations_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_type_1257_, lean_object* v_k_1258_, lean_object* v_cleanupAnnotations_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1266_; lean_object* v_res_1267_; 
v_cleanupAnnotations_boxed_1266_ = lean_unbox(v_cleanupAnnotations_1259_);
v_res_1267_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0(v_00_u03b1_1256_, v_type_1257_, v_k_1258_, v_cleanupAnnotations_boxed_1266_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v_head_1273_, lean_object* v_name_1274_, lean_object* v_lparams_1275_, lean_object* v_params_1276_, lean_object* v_compFieldVars_1277_, lean_object* v_fields_1278_, lean_object* v_retTy_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v_head_1273_);
v___x_1286_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_1273_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_nargs_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v_dummy_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; lean_object* v___y_1300_; uint8_t v___x_1324_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref(v___x_1286_);
v_nargs_1288_ = l_Lean_Expr_getAppNumArgs(v_retTy_1279_);
v___x_1289_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
v___x_1290_ = l_Lean_Name_append(v_name_1274_, v___x_1289_);
v___x_1291_ = l_Lean_mkConst(v___x_1290_, v_lparams_1275_);
v_dummy_1292_ = lean_obj_once(&l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4, &l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4_once, _init_l_Lean_Elab_ComputedFields_getComputedFieldValue___closed__4);
lean_inc(v_nargs_1288_);
v___x_1293_ = lean_mk_array(v_nargs_1288_, v_dummy_1292_);
v___x_1294_ = lean_unsigned_to_nat(1u);
v___x_1295_ = lean_nat_sub(v_nargs_1288_, v___x_1294_);
lean_dec(v_nargs_1288_);
v___x_1296_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_retTy_1279_, v___x_1293_, v___x_1295_);
v___x_1297_ = l_Lean_mkAppN(v___x_1291_, v___x_1296_);
lean_dec_ref(v___x_1296_);
v___x_1298_ = 1;
v___x_1324_ = lean_unbox(v_a_1287_);
lean_dec(v_a_1287_);
if (v___x_1324_ == 0)
{
v___y_1300_ = v_compFieldVars_1277_;
goto v___jp_1299_;
}
else
{
lean_object* v___x_1325_; 
lean_dec_ref(v_compFieldVars_1277_);
v___x_1325_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___y_1300_ = v___x_1325_;
goto v___jp_1299_;
}
v___jp_1299_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; uint8_t v___x_1304_; lean_object* v___x_1305_; 
v___x_1301_ = l_Array_append___redArg(v_params_1276_, v___y_1300_);
lean_dec_ref(v___y_1300_);
v___x_1302_ = l_Array_append___redArg(v___x_1301_, v_fields_1278_);
v___x_1303_ = 0;
v___x_1304_ = 1;
v___x_1305_ = l_Lean_Meta_mkForallFVars(v___x_1302_, v___x_1297_, v___x_1303_, v___x_1298_, v___x_1298_, v___x_1304_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___x_1302_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1315_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1315_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1315_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1310_ = l_Lean_Name_append(v_head_1273_, v___x_1289_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_a_1306_);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1311_);
v___x_1313_ = v___x_1308_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v_head_1273_);
v_a_1316_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1305_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1305_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v_retTy_1279_);
lean_dec_ref(v_compFieldVars_1277_);
lean_dec_ref(v_params_1276_);
lean_dec(v_lparams_1275_);
lean_dec(v_name_1274_);
lean_dec(v_head_1273_);
v_a_1326_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1286_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1286_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed(lean_object* v_head_1334_, lean_object* v_name_1335_, lean_object* v_lparams_1336_, lean_object* v_params_1337_, lean_object* v_compFieldVars_1338_, lean_object* v_fields_1339_, lean_object* v_retTy_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(v_head_1334_, v_name_1335_, v_lparams_1336_, v_params_1337_, v_compFieldVars_1338_, v_fields_1339_, v_retTy_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec_ref(v_fields_1339_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(lean_object* v_name_1348_, lean_object* v_lparams_1349_, lean_object* v_params_1350_, lean_object* v_compFieldVars_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
if (lean_obj_tag(v_x_1352_) == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec_ref(v_compFieldVars_1351_);
lean_dec_ref(v_params_1350_);
lean_dec(v_lparams_1349_);
lean_dec(v_name_1348_);
v___x_1360_ = l_List_reverse___redArg(v_x_1353_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1360_);
return v___x_1361_;
}
else
{
lean_object* v_head_1362_; lean_object* v_tail_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1395_; 
v_head_1362_ = lean_ctor_get(v_x_1352_, 0);
v_tail_1363_ = lean_ctor_get(v_x_1352_, 1);
v_isSharedCheck_1395_ = !lean_is_exclusive(v_x_1352_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1365_ = v_x_1352_;
v_isShared_1366_ = v_isSharedCheck_1395_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_tail_1363_);
lean_inc(v_head_1362_);
lean_dec(v_x_1352_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1395_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
lean_inc(v_lparams_1349_);
lean_inc(v_head_1362_);
v___x_1367_ = l_Lean_mkConst(v_head_1362_, v_lparams_1349_);
v___x_1368_ = l_Lean_mkAppN(v___x_1367_, v_params_1350_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
v___x_1369_ = lean_infer_type(v___x_1368_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___f_1371_; uint8_t v___x_1372_; lean_object* v___x_1373_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_a_1370_);
lean_dec_ref(v___x_1369_);
lean_inc_ref(v_compFieldVars_1351_);
lean_inc_ref(v_params_1350_);
lean_inc(v_lparams_1349_);
lean_inc(v_name_1348_);
v___f_1371_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1371_, 0, v_head_1362_);
lean_closure_set(v___f_1371_, 1, v_name_1348_);
lean_closure_set(v___f_1371_, 2, v_lparams_1349_);
lean_closure_set(v___f_1371_, 3, v_params_1350_);
lean_closure_set(v___f_1371_, 4, v_compFieldVars_1351_);
v___x_1372_ = 0;
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
lean_inc_ref(v___y_1354_);
v___x_1373_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1370_, v___f_1371_, v___x_1372_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1376_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref(v___x_1373_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_x_1353_);
lean_ctor_set(v___x_1365_, 0, v_a_1374_);
v___x_1376_ = v___x_1365_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1374_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_x_1353_);
v___x_1376_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
v_x_1352_ = v_tail_1363_;
v_x_1353_ = v___x_1376_;
goto _start;
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_del_object(v___x_1365_);
lean_dec(v_tail_1363_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v_x_1353_);
lean_dec_ref(v_compFieldVars_1351_);
lean_dec_ref(v_params_1350_);
lean_dec(v_lparams_1349_);
lean_dec(v_name_1348_);
v_a_1379_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1373_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1373_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_del_object(v___x_1365_);
lean_dec(v_tail_1363_);
lean_dec(v_head_1362_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v_x_1353_);
lean_dec_ref(v_compFieldVars_1351_);
lean_dec_ref(v_params_1350_);
lean_dec(v_lparams_1349_);
lean_dec(v_name_1348_);
v_a_1387_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1369_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1369_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___boxed(lean_object* v_name_1396_, lean_object* v_lparams_1397_, lean_object* v_params_1398_, lean_object* v_compFieldVars_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v_name_1396_, v_lparams_1397_, v_params_1398_, v_compFieldVars_1399_, v_x_1400_, v_x_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_toInductiveVal_1415_; lean_object* v_toConstantVal_1416_; lean_object* v_lparams_1417_; lean_object* v_params_1418_; lean_object* v_compFieldVars_1419_; lean_object* v_numParams_1420_; lean_object* v_ctors_1421_; uint8_t v_isUnsafe_1422_; lean_object* v_name_1423_; lean_object* v_levelParams_1424_; lean_object* v_type_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1449_; 
v_toInductiveVal_1415_ = lean_ctor_get(v_a_1409_, 0);
v_toConstantVal_1416_ = lean_ctor_get(v_toInductiveVal_1415_, 0);
lean_inc_ref(v_toConstantVal_1416_);
v_lparams_1417_ = lean_ctor_get(v_a_1409_, 1);
lean_inc(v_lparams_1417_);
v_params_1418_ = lean_ctor_get(v_a_1409_, 2);
lean_inc_ref(v_params_1418_);
v_compFieldVars_1419_ = lean_ctor_get(v_a_1409_, 4);
lean_inc_ref(v_compFieldVars_1419_);
v_numParams_1420_ = lean_ctor_get(v_toInductiveVal_1415_, 1);
lean_inc(v_numParams_1420_);
v_ctors_1421_ = lean_ctor_get(v_toInductiveVal_1415_, 4);
lean_inc(v_ctors_1421_);
v_isUnsafe_1422_ = lean_ctor_get_uint8(v_toInductiveVal_1415_, sizeof(void*)*6 + 1);
v_name_1423_ = lean_ctor_get(v_toConstantVal_1416_, 0);
v_levelParams_1424_ = lean_ctor_get(v_toConstantVal_1416_, 1);
v_type_1425_ = lean_ctor_get(v_toConstantVal_1416_, 2);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_toConstantVal_1416_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1427_ = v_toConstantVal_1416_;
v_isShared_1428_ = v_isSharedCheck_1449_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_type_1425_);
lean_inc(v_levelParams_1424_);
lean_inc(v_name_1423_);
lean_dec(v_toConstantVal_1416_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1449_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_box(0);
lean_inc(v_a_1413_);
lean_inc_ref(v_a_1412_);
lean_inc(v_name_1423_);
v___x_1430_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v_name_1423_, v_lparams_1417_, v_params_1418_, v_compFieldVars_1419_, v_ctors_1421_, v___x_1429_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
if (lean_obj_tag(v___x_1430_) == 0)
{
lean_object* v_a_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1435_; 
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
v___x_1433_ = l_Lean_Name_append(v_name_1423_, v___x_1432_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 2, v_a_1431_);
lean_ctor_set(v___x_1427_, 1, v_type_1425_);
lean_ctor_set(v___x_1427_, 0, v___x_1433_);
v___x_1435_ = v___x_1427_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1433_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_type_1425_);
lean_ctor_set(v_reuseFailAlloc_1440_, 2, v_a_1431_);
v___x_1435_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; lean_object* v___x_1439_; 
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___x_1429_);
v___x_1437_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1437_, 0, v_levelParams_1424_);
lean_ctor_set(v___x_1437_, 1, v_numParams_1420_);
lean_ctor_set(v___x_1437_, 2, v___x_1436_);
lean_ctor_set_uint8(v___x_1437_, sizeof(void*)*3, v_isUnsafe_1422_);
v___x_1438_ = 0;
v___x_1439_ = l_Lean_addDecl(v___x_1437_, v___x_1438_, v_a_1412_, v_a_1413_);
return v___x_1439_;
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_del_object(v___x_1427_);
lean_dec_ref(v_type_1425_);
lean_dec(v_levelParams_1424_);
lean_dec(v_name_1423_);
lean_dec(v_numParams_1420_);
lean_dec(v_a_1413_);
lean_dec_ref(v_a_1412_);
v_a_1441_ = lean_ctor_get(v___x_1430_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1430_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1430_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1430_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_, lean_object* v_a_1453_, lean_object* v_a_1454_, lean_object* v_a_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1450_, v_a_1451_, v_a_1452_, v_a_1453_, v_a_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1457_, lean_object* v___y_1458_, lean_object* v_b_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = lean_apply_7(v_k_1457_, v_b_1459_, v___y_1458_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, lean_box(0));
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1466_, lean_object* v___y_1467_, lean_object* v_b_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1466_, v___y_1467_, v_b_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1475_, lean_object* v_type_1476_, lean_object* v_val_1477_, lean_object* v_k_1478_, uint8_t v_nondep_1479_, uint8_t v_kind_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___f_1487_; lean_object* v___x_1488_; 
v___f_1487_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1487_, 0, v_k_1478_);
lean_closure_set(v___f_1487_, 1, v___y_1481_);
v___x_1488_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1475_, v_type_1476_, v_val_1477_, v___f_1487_, v_nondep_1479_, v_kind_1480_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1488_) == 0)
{
return v___x_1488_;
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1497_, lean_object* v_type_1498_, lean_object* v_val_1499_, lean_object* v_k_1500_, lean_object* v_nondep_1501_, lean_object* v_kind_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
uint8_t v_nondep_boxed_1509_; uint8_t v_kind_boxed_1510_; lean_object* v_res_1511_; 
v_nondep_boxed_1509_ = lean_unbox(v_nondep_1501_);
v_kind_boxed_1510_ = lean_unbox(v_kind_1502_);
v_res_1511_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1497_, v_type_1498_, v_val_1499_, v_k_1500_, v_nondep_boxed_1509_, v_kind_boxed_1510_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1512_, lean_object* v_name_1513_, lean_object* v_type_1514_, lean_object* v_val_1515_, lean_object* v_k_1516_, uint8_t v_nondep_1517_, uint8_t v_kind_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1513_, v_type_1514_, v_val_1515_, v_k_1516_, v_nondep_1517_, v_kind_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_name_1527_, lean_object* v_type_1528_, lean_object* v_val_1529_, lean_object* v_k_1530_, lean_object* v_nondep_1531_, lean_object* v_kind_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
uint8_t v_nondep_boxed_1539_; uint8_t v_kind_boxed_1540_; lean_object* v_res_1541_; 
v_nondep_boxed_1539_ = lean_unbox(v_nondep_1531_);
v_kind_boxed_1540_ = lean_unbox(v_kind_1532_);
v_res_1541_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1526_, v_name_1527_, v_type_1528_, v_val_1529_, v_k_1530_, v_nondep_boxed_1539_, v_kind_boxed_1540_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1542_, lean_object* v___x_1543_, lean_object* v_majorImpl_1544_, lean_object* v_m_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; uint8_t v___x_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1552_ = lean_mk_empty_array_with_capacity(v___x_1542_);
lean_inc_ref(v_m_1545_);
lean_inc_ref(v___x_1552_);
v___x_1553_ = lean_array_push(v___x_1552_, v_m_1545_);
v___x_1554_ = l_Array_append___redArg(v___x_1553_, v___x_1543_);
v___x_1555_ = lean_array_push(v___x_1552_, v_majorImpl_1544_);
v___x_1556_ = l_Array_append___redArg(v___x_1554_, v___x_1555_);
lean_dec_ref(v___x_1555_);
v___x_1557_ = 0;
v___x_1558_ = 1;
v___x_1559_ = 1;
v___x_1560_ = l_Lean_Meta_mkLambdaFVars(v___x_1556_, v_m_1545_, v___x_1557_, v___x_1558_, v___x_1557_, v___x_1558_, v___x_1559_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_);
lean_dec_ref(v___x_1556_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1561_, lean_object* v___x_1562_, lean_object* v_majorImpl_1563_, lean_object* v_m_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1561_, v___x_1562_, v_majorImpl_1563_, v_m_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v___x_1562_);
lean_dec(v___x_1561_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v_constMotive_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, lean_object* v_majorImpl_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; 
lean_inc(v___y_1583_);
lean_inc_ref(v___y_1582_);
lean_inc(v___y_1581_);
lean_inc_ref(v___y_1580_);
lean_inc_ref(v_constMotive_1575_);
v___x_1585_ = lean_infer_type(v_constMotive_1575_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v___f_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; uint8_t v___x_1590_; lean_object* v___x_1591_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1585_);
v___f_1587_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1587_, 0, v___x_1576_);
lean_closure_set(v___f_1587_, 1, v___x_1577_);
lean_closure_set(v___f_1587_, 2, v_majorImpl_1578_);
v___x_1588_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1589_ = 0;
v___x_1590_ = 0;
v___x_1591_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1588_, v_a_1586_, v_constMotive_1575_, v___f_1587_, v___x_1589_, v___x_1590_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
return v___x_1591_;
}
else
{
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec_ref(v___y_1579_);
lean_dec_ref(v_majorImpl_1578_);
lean_dec_ref(v___x_1577_);
lean_dec(v___x_1576_);
lean_dec_ref(v_constMotive_1575_);
return v___x_1585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v_constMotive_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v_majorImpl_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v_constMotive_1592_, v___x_1593_, v___x_1594_, v_majorImpl_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1603_, uint8_t v_bi_1604_, lean_object* v_type_1605_, lean_object* v_k_1606_, uint8_t v_kind_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1615_; 
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1614_, 0, v_k_1606_);
lean_closure_set(v___f_1614_, 1, v___y_1608_);
v___x_1615_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1603_, v_bi_1604_, v_type_1605_, v___f_1614_, v_kind_1607_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1615_) == 0)
{
return v___x_1615_;
}
else
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1624_, lean_object* v_bi_1625_, lean_object* v_type_1626_, lean_object* v_k_1627_, lean_object* v_kind_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_){
_start:
{
uint8_t v_bi_boxed_1635_; uint8_t v_kind_boxed_1636_; lean_object* v_res_1637_; 
v_bi_boxed_1635_ = lean_unbox(v_bi_1625_);
v_kind_boxed_1636_ = lean_unbox(v_kind_1628_);
v_res_1637_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1624_, v_bi_boxed_1635_, v_type_1626_, v_k_1627_, v_kind_boxed_1636_, v___y_1629_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1638_, lean_object* v_type_1639_, lean_object* v_k_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_){
_start:
{
uint8_t v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = 0;
v___x_1648_ = 0;
v___x_1649_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1638_, v___x_1647_, v_type_1639_, v_k_1640_, v___x_1648_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1650_, lean_object* v_type_1651_, lean_object* v_k_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1650_, v_type_1651_, v_k_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
if (lean_obj_tag(v_a_1660_) == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = l_List_reverse___redArg(v_a_1661_);
return v___x_1662_;
}
else
{
lean_object* v_head_1663_; lean_object* v_tail_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1673_; 
v_head_1663_ = lean_ctor_get(v_a_1660_, 0);
v_tail_1664_ = lean_ctor_get(v_a_1660_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_a_1660_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1666_ = v_a_1660_;
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_tail_1664_);
lean_inc(v_head_1663_);
lean_dec(v_a_1660_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1673_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1668_; lean_object* v___x_1670_; 
v___x_1668_ = l_Lean_mkLevelParam(v_head_1663_);
if (v_isShared_1667_ == 0)
{
lean_ctor_set(v___x_1666_, 1, v_a_1661_);
lean_ctor_set(v___x_1666_, 0, v___x_1668_);
v___x_1670_ = v___x_1666_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_a_1661_);
v___x_1670_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
v_a_1660_ = v_tail_1664_;
v_a_1661_ = v___x_1670_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1674_, lean_object* v_b_1675_){
_start:
{
lean_object* v_array_1676_; lean_object* v_start_1677_; lean_object* v_stop_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1691_; 
v_array_1676_ = lean_ctor_get(v_a_1674_, 0);
v_start_1677_ = lean_ctor_get(v_a_1674_, 1);
v_stop_1678_ = lean_ctor_get(v_a_1674_, 2);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_a_1674_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1680_ = v_a_1674_;
v_isShared_1681_ = v_isSharedCheck_1691_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_stop_1678_);
lean_inc(v_start_1677_);
lean_inc(v_array_1676_);
lean_dec(v_a_1674_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1691_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_nat_dec_lt(v_start_1677_, v_stop_1678_);
if (v___x_1682_ == 0)
{
lean_del_object(v___x_1680_);
lean_dec(v_stop_1678_);
lean_dec(v_start_1677_);
lean_dec_ref(v_array_1676_);
return v_b_1675_;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = lean_nat_add(v_start_1677_, v___x_1683_);
lean_inc_ref(v_array_1676_);
if (v_isShared_1681_ == 0)
{
lean_ctor_set(v___x_1680_, 1, v___x_1684_);
v___x_1686_ = v___x_1680_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_array_1676_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_stop_1678_);
v___x_1686_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1687_ = lean_array_fget(v_array_1676_, v_start_1677_);
lean_dec(v_start_1677_);
lean_dec_ref(v_array_1676_);
v___x_1688_ = lean_array_push(v_b_1675_, v___x_1687_);
v_a_1674_ = v___x_1686_;
v_b_1675_ = v___x_1688_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1692_, lean_object* v_a_1693_, lean_object* v_constMotive_1694_, uint8_t v___x_1695_, lean_object* v_compFieldVars_1696_, lean_object* v_args_1697_, lean_object* v_x_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
v___x_1705_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1692_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = l_Lean_mkAppN(v_a_1693_, v_args_1697_);
lean_inc(v___y_1703_);
lean_inc_ref(v___y_1702_);
lean_inc(v___y_1701_);
lean_inc_ref(v___y_1700_);
v___x_1708_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1694_, v___x_1707_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___y_1711_; uint8_t v___x_1716_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___x_1708_);
v___x_1716_ = lean_unbox(v_a_1706_);
lean_dec(v_a_1706_);
if (v___x_1716_ == 0)
{
v___y_1711_ = v_compFieldVars_1696_;
goto v___jp_1710_;
}
else
{
lean_object* v___x_1717_; 
lean_dec_ref(v_compFieldVars_1696_);
v___x_1717_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___y_1711_ = v___x_1717_;
goto v___jp_1710_;
}
v___jp_1710_:
{
lean_object* v___x_1712_; uint8_t v___x_1713_; uint8_t v___x_1714_; lean_object* v___x_1715_; 
v___x_1712_ = l_Array_append___redArg(v___y_1711_, v_args_1697_);
v___x_1713_ = 0;
v___x_1714_ = 1;
v___x_1715_ = l_Lean_Meta_mkLambdaFVars(v___x_1712_, v_a_1709_, v___x_1713_, v___x_1695_, v___x_1713_, v___x_1695_, v___x_1714_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v___x_1712_);
return v___x_1715_;
}
}
else
{
lean_dec(v_a_1706_);
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v_compFieldVars_1696_);
return v___x_1708_;
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
lean_dec(v___y_1703_);
lean_dec_ref(v___y_1702_);
lean_dec(v___y_1701_);
lean_dec_ref(v___y_1700_);
lean_dec_ref(v_compFieldVars_1696_);
lean_dec_ref(v_constMotive_1694_);
lean_dec_ref(v_a_1693_);
v_a_1718_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1705_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1705_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1723_; 
if (v_isShared_1721_ == 0)
{
v___x_1723_ = v___x_1720_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_a_1718_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1726_, lean_object* v_a_1727_, lean_object* v_constMotive_1728_, lean_object* v___x_1729_, lean_object* v_compFieldVars_1730_, lean_object* v_args_1731_, lean_object* v_x_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v___x_12739__boxed_1739_; lean_object* v_res_1740_; 
v___x_12739__boxed_1739_ = lean_unbox(v___x_1729_);
v_res_1740_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1726_, v_a_1727_, v_constMotive_1728_, v___x_12739__boxed_1739_, v_compFieldVars_1730_, v_args_1731_, v_x_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v_x_1732_);
lean_dec_ref(v_args_1731_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1741_, lean_object* v_compFieldVars_1742_, lean_object* v_as_1743_, lean_object* v_bs_1744_, lean_object* v_i_1745_, lean_object* v_cs_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_){
_start:
{
lean_object* v___y_1754_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v___x_1768_ = lean_array_get_size(v_as_1743_);
v___x_1769_ = lean_nat_dec_lt(v_i_1745_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___x_1770_; 
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v_i_1745_);
lean_dec_ref(v_compFieldVars_1742_);
lean_dec_ref(v_constMotive_1741_);
v___x_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1770_, 0, v_cs_1746_);
return v___x_1770_;
}
else
{
lean_object* v___x_1771_; uint8_t v___x_1772_; 
v___x_1771_ = lean_array_get_size(v_bs_1744_);
v___x_1772_ = lean_nat_dec_lt(v_i_1745_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v_i_1745_);
lean_dec_ref(v_compFieldVars_1742_);
lean_dec_ref(v_constMotive_1741_);
v___x_1773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_cs_1746_);
return v___x_1773_;
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1775_; 
v_a_1774_ = lean_array_fget_borrowed(v_as_1743_, v_i_1745_);
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc(v_a_1774_);
v___x_1775_ = lean_infer_type(v_a_1774_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v_b_1777_; lean_object* v___x_1778_; lean_object* v___f_1779_; uint8_t v___x_1780_; lean_object* v___x_1781_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v_b_1777_ = lean_array_fget_borrowed(v_bs_1744_, v_i_1745_);
v___x_1778_ = lean_box(v___x_1772_);
lean_inc_ref(v_compFieldVars_1742_);
lean_inc_ref(v_constMotive_1741_);
lean_inc(v_a_1774_);
lean_inc(v_b_1777_);
v___f_1779_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1779_, 0, v_b_1777_);
lean_closure_set(v___f_1779_, 1, v_a_1774_);
lean_closure_set(v___f_1779_, 2, v_constMotive_1741_);
lean_closure_set(v___f_1779_, 3, v___x_1778_);
lean_closure_set(v___f_1779_, 4, v_compFieldVars_1742_);
v___x_1780_ = 0;
lean_inc(v___y_1751_);
lean_inc_ref(v___y_1750_);
lean_inc(v___y_1749_);
lean_inc_ref(v___y_1748_);
lean_inc_ref(v___y_1747_);
v___x_1781_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1776_, v___f_1779_, v___x_1780_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_);
v___y_1754_ = v___x_1781_;
goto v___jp_1753_;
}
else
{
v___y_1754_ = v___x_1775_;
goto v___jp_1753_;
}
}
}
v___jp_1753_:
{
if (lean_obj_tag(v___y_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v_a_1755_ = lean_ctor_get(v___y_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___y_1754_);
v___x_1756_ = lean_unsigned_to_nat(1u);
v___x_1757_ = lean_nat_add(v_i_1745_, v___x_1756_);
lean_dec(v_i_1745_);
v___x_1758_ = lean_array_push(v_cs_1746_, v_a_1755_);
v_i_1745_ = v___x_1757_;
v_cs_1746_ = v___x_1758_;
goto _start;
}
else
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1767_; 
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec_ref(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec_ref(v_cs_1746_);
lean_dec(v_i_1745_);
lean_dec_ref(v_compFieldVars_1742_);
lean_dec_ref(v_constMotive_1741_);
v_a_1760_ = lean_ctor_get(v___y_1754_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___y_1754_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1762_ = v___y_1754_;
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___y_1754_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1767_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
lean_object* v___x_1765_; 
if (v_isShared_1763_ == 0)
{
v___x_1765_ = v___x_1762_;
goto v_reusejp_1764_;
}
else
{
lean_object* v_reuseFailAlloc_1766_; 
v_reuseFailAlloc_1766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1766_, 0, v_a_1760_);
v___x_1765_ = v_reuseFailAlloc_1766_;
goto v_reusejp_1764_;
}
v_reusejp_1764_:
{
return v___x_1765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1782_, lean_object* v_compFieldVars_1783_, lean_object* v_as_1784_, lean_object* v_bs_1785_, lean_object* v_i_1786_, lean_object* v_cs_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1782_, v_compFieldVars_1783_, v_as_1784_, v_bs_1785_, v_i_1786_, v_cs_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec_ref(v_bs_1785_);
lean_dec_ref(v_as_1784_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1798_, lean_object* v___x_1799_, lean_object* v___x_1800_, lean_object* v_lparams_1801_, lean_object* v_params_1802_, lean_object* v_ctors_1803_, lean_object* v_compFieldVars_1804_, lean_object* v_levelParams_1805_, lean_object* v_xs_1806_, lean_object* v_constMotive_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___f_1820_; lean_object* v___x_1821_; lean_object* v___y_1823_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1814_ = lean_unsigned_to_nat(1u);
v___x_1815_ = lean_nat_add(v_numIndices_1798_, v___x_1814_);
lean_inc(v___x_1815_);
lean_inc_ref(v_xs_1806_);
v___x_1816_ = l_Array_toSubarray___redArg(v_xs_1806_, v___x_1814_, v___x_1815_);
v___x_1817_ = lean_unsigned_to_nat(0u);
v___x_1818_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_1819_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1816_, v___x_1818_);
lean_inc_ref(v___x_1819_);
lean_inc_ref(v_constMotive_1807_);
v___f_1820_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1820_, 0, v_constMotive_1807_);
lean_closure_set(v___f_1820_, 1, v___x_1814_);
lean_closure_set(v___f_1820_, 2, v___x_1819_);
v___x_1821_ = lean_array_get_borrowed(v___x_1799_, v_xs_1806_, v___x_1815_);
lean_dec(v___x_1815_);
v___x_1864_ = lean_unsigned_to_nat(2u);
v___x_1865_ = lean_nat_add(v_numIndices_1798_, v___x_1864_);
v___x_1866_ = lean_array_get_size(v_xs_1806_);
v___x_1867_ = lean_nat_dec_le(v___x_1865_, v___x_1817_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1865_);
lean_ctor_set(v___x_1868_, 1, v___x_1866_);
v___y_1823_ = v___x_1868_;
goto v___jp_1822_;
}
else
{
lean_object* v___x_1869_; 
lean_dec(v___x_1865_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1817_);
lean_ctor_set(v___x_1869_, 1, v___x_1866_);
v___y_1823_ = v___x_1869_;
goto v___jp_1822_;
}
v___jp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_inc(v___x_1800_);
v___x_1824_ = l_Lean_mkConst(v___x_1800_, v_lparams_1801_);
lean_inc_ref(v_params_1802_);
v___x_1825_ = l_Array_append___redArg(v_params_1802_, v___x_1819_);
v___x_1826_ = l_Lean_mkAppN(v___x_1824_, v___x_1825_);
lean_dec_ref(v___x_1825_);
v___x_1827_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
lean_inc_ref(v___y_1808_);
lean_inc_ref(v___x_1826_);
v___x_1828_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1827_, v___x_1826_, v___f_1820_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_1828_) == 0)
{
lean_object* v_a_1829_; lean_object* v___x_1830_; 
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
lean_inc(v_a_1829_);
lean_dec_ref(v___x_1828_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
lean_inc(v___x_1821_);
v___x_1830_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1826_, v___x_1821_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_1830_) == 0)
{
lean_object* v_a_1831_; lean_object* v_lower_1832_; lean_object* v_upper_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v_a_1831_ = lean_ctor_get(v___x_1830_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1830_);
v_lower_1832_ = lean_ctor_get(v___y_1823_, 0);
lean_inc(v_lower_1832_);
v_upper_1833_ = lean_ctor_get(v___y_1823_, 1);
lean_inc(v_upper_1833_);
lean_dec_ref(v___y_1823_);
lean_inc_ref(v_xs_1806_);
v___x_1834_ = l_Array_toSubarray___redArg(v_xs_1806_, v_lower_1832_, v_upper_1833_);
v___x_1835_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1834_, v___x_1818_);
v___x_1836_ = lean_array_mk(v_ctors_1803_);
lean_inc(v___y_1812_);
lean_inc_ref(v___y_1811_);
lean_inc(v___y_1810_);
lean_inc_ref(v___y_1809_);
v___x_1837_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1807_, v_compFieldVars_1804_, v___x_1835_, v___x_1836_, v___x_1817_, v___x_1818_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec_ref(v___x_1836_);
lean_dec_ref(v___x_1835_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; uint8_t v___x_1853_; uint8_t v___x_1854_; lean_object* v___x_1855_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
lean_inc_ref(v_params_1802_);
v___x_1839_ = l_Array_append___redArg(v_params_1802_, v_xs_1806_);
lean_dec_ref(v_xs_1806_);
v___x_1840_ = l_Lean_mkCasesOnName(v___x_1800_);
v___x_1841_ = lean_box(0);
v___x_1842_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1805_, v___x_1841_);
v___x_1843_ = l_Lean_mkConst(v___x_1840_, v___x_1842_);
v___x_1844_ = lean_mk_empty_array_with_capacity(v___x_1814_);
lean_inc_ref(v___x_1844_);
v___x_1845_ = lean_array_push(v___x_1844_, v_a_1829_);
v___x_1846_ = l_Array_append___redArg(v_params_1802_, v___x_1845_);
lean_dec_ref(v___x_1845_);
v___x_1847_ = l_Array_append___redArg(v___x_1846_, v___x_1819_);
lean_dec_ref(v___x_1819_);
v___x_1848_ = lean_array_push(v___x_1844_, v_a_1831_);
v___x_1849_ = l_Array_append___redArg(v___x_1847_, v___x_1848_);
lean_dec_ref(v___x_1848_);
v___x_1850_ = l_Array_append___redArg(v___x_1849_, v_a_1838_);
lean_dec(v_a_1838_);
v___x_1851_ = l_Lean_mkAppN(v___x_1843_, v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1852_ = 0;
v___x_1853_ = 1;
v___x_1854_ = 1;
v___x_1855_ = l_Lean_Meta_mkLambdaFVars(v___x_1839_, v___x_1851_, v___x_1852_, v___x_1853_, v___x_1852_, v___x_1853_, v___x_1854_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___x_1839_);
return v___x_1855_;
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_dec(v_a_1831_);
lean_dec(v_a_1829_);
lean_dec_ref(v___x_1819_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v_xs_1806_);
lean_dec(v_levelParams_1805_);
lean_dec_ref(v_params_1802_);
lean_dec(v___x_1800_);
v_a_1856_ = lean_ctor_get(v___x_1837_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1837_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1837_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_dec(v_a_1829_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v___x_1819_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_constMotive_1807_);
lean_dec_ref(v_xs_1806_);
lean_dec(v_levelParams_1805_);
lean_dec_ref(v_compFieldVars_1804_);
lean_dec(v_ctors_1803_);
lean_dec_ref(v_params_1802_);
lean_dec(v___x_1800_);
return v___x_1830_;
}
}
else
{
lean_dec_ref(v___x_1826_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v___x_1819_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v___y_1808_);
lean_dec_ref(v_constMotive_1807_);
lean_dec_ref(v_xs_1806_);
lean_dec(v_levelParams_1805_);
lean_dec_ref(v_compFieldVars_1804_);
lean_dec(v_ctors_1803_);
lean_dec_ref(v_params_1802_);
lean_dec(v___x_1800_);
return v___x_1828_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1870_, lean_object* v___x_1871_, lean_object* v___x_1872_, lean_object* v_lparams_1873_, lean_object* v_params_1874_, lean_object* v_ctors_1875_, lean_object* v_compFieldVars_1876_, lean_object* v_levelParams_1877_, lean_object* v_xs_1878_, lean_object* v_constMotive_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1870_, v___x_1871_, v___x_1872_, v_lparams_1873_, v_params_1874_, v_ctors_1875_, v_compFieldVars_1876_, v_levelParams_1877_, v_xs_1878_, v_constMotive_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
lean_dec(v_numIndices_1870_);
return v_res_1886_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1888_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1889_, 0, v___x_1888_);
return v___x_1889_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1893_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1892_);
lean_ctor_set(v___x_1893_, 2, v___x_1892_);
lean_ctor_set(v___x_1893_, 3, v___x_1892_);
lean_ctor_set(v___x_1893_, 4, v___x_1892_);
lean_ctor_set(v___x_1893_, 5, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v___x_1898_; lean_object* v_nextMacroScope_1899_; lean_object* v_ngen_1900_; lean_object* v_auxDeclNGen_1901_; lean_object* v_traceState_1902_; lean_object* v_messages_1903_; lean_object* v_infoState_1904_; lean_object* v_snapshotTasks_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1931_; 
v___x_1898_ = lean_st_ref_take(v___y_1896_);
v_nextMacroScope_1899_ = lean_ctor_get(v___x_1898_, 1);
v_ngen_1900_ = lean_ctor_get(v___x_1898_, 2);
v_auxDeclNGen_1901_ = lean_ctor_get(v___x_1898_, 3);
v_traceState_1902_ = lean_ctor_get(v___x_1898_, 4);
v_messages_1903_ = lean_ctor_get(v___x_1898_, 6);
v_infoState_1904_ = lean_ctor_get(v___x_1898_, 7);
v_snapshotTasks_1905_ = lean_ctor_get(v___x_1898_, 8);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; lean_object* v_unused_1933_; 
v_unused_1932_ = lean_ctor_get(v___x_1898_, 5);
lean_dec(v_unused_1932_);
v_unused_1933_ = lean_ctor_get(v___x_1898_, 0);
lean_dec(v_unused_1933_);
v___x_1907_ = v___x_1898_;
v_isShared_1908_ = v_isSharedCheck_1931_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_snapshotTasks_1905_);
lean_inc(v_infoState_1904_);
lean_inc(v_messages_1903_);
lean_inc(v_traceState_1902_);
lean_inc(v_auxDeclNGen_1901_);
lean_inc(v_ngen_1900_);
lean_inc(v_nextMacroScope_1899_);
lean_dec(v___x_1898_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1931_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 5, v___x_1909_);
lean_ctor_set(v___x_1907_, 0, v_env_1894_);
v___x_1911_ = v___x_1907_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_env_1894_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_nextMacroScope_1899_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_ngen_1900_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_auxDeclNGen_1901_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_traceState_1902_);
lean_ctor_set(v_reuseFailAlloc_1930_, 5, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1930_, 6, v_messages_1903_);
lean_ctor_set(v_reuseFailAlloc_1930_, 7, v_infoState_1904_);
lean_ctor_set(v_reuseFailAlloc_1930_, 8, v_snapshotTasks_1905_);
v___x_1911_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v_mctx_1914_; lean_object* v_zetaDeltaFVarIds_1915_; lean_object* v_postponed_1916_; lean_object* v_diag_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1928_; 
v___x_1912_ = lean_st_ref_set(v___y_1896_, v___x_1911_);
v___x_1913_ = lean_st_ref_take(v___y_1895_);
v_mctx_1914_ = lean_ctor_get(v___x_1913_, 0);
v_zetaDeltaFVarIds_1915_ = lean_ctor_get(v___x_1913_, 2);
v_postponed_1916_ = lean_ctor_get(v___x_1913_, 3);
v_diag_1917_ = lean_ctor_get(v___x_1913_, 4);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1928_ == 0)
{
lean_object* v_unused_1929_; 
v_unused_1929_ = lean_ctor_get(v___x_1913_, 1);
lean_dec(v_unused_1929_);
v___x_1919_ = v___x_1913_;
v_isShared_1920_ = v_isSharedCheck_1928_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_diag_1917_);
lean_inc(v_postponed_1916_);
lean_inc(v_zetaDeltaFVarIds_1915_);
lean_inc(v_mctx_1914_);
lean_dec(v___x_1913_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1928_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1921_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 1, v___x_1921_);
v___x_1923_ = v___x_1919_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_mctx_1914_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_zetaDeltaFVarIds_1915_);
lean_ctor_set(v_reuseFailAlloc_1927_, 3, v_postponed_1916_);
lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_diag_1917_);
v___x_1923_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = lean_st_ref_set(v___y_1895_, v___x_1923_);
v___x_1925_ = lean_box(0);
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1925_);
return v___x_1926_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_){
_start:
{
lean_object* v_res_1938_; 
v_res_1938_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec(v___y_1935_);
return v_res_1938_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1939_, lean_object* v_impName_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_){
_start:
{
lean_object* v___x_1947_; lean_object* v_env_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_st_ref_get(v___y_1945_);
v_env_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc_ref(v_env_1948_);
lean_dec(v___x_1947_);
v___x_1949_ = l_Lean_Compiler_setImplementedBy(v_env_1948_, v_declName_1939_, v_impName_1940_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1952_; uint8_t v_isShared_1953_; uint8_t v_isSharedCheck_1959_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1952_ = v___x_1949_;
v_isShared_1953_ = v_isSharedCheck_1959_;
goto v_resetjp_1951_;
}
else
{
lean_inc(v_a_1950_);
lean_dec(v___x_1949_);
v___x_1952_ = lean_box(0);
v_isShared_1953_ = v_isSharedCheck_1959_;
goto v_resetjp_1951_;
}
v_resetjp_1951_:
{
lean_object* v___x_1955_; 
if (v_isShared_1953_ == 0)
{
lean_ctor_set_tag(v___x_1952_, 3);
v___x_1955_ = v___x_1952_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1950_);
v___x_1955_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = l_Lean_MessageData_ofFormat(v___x_1955_);
v___x_1957_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1956_, v___y_1942_, v___y_1943_, v___y_1944_, v___y_1945_);
return v___x_1957_;
}
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1949_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1949_);
v___x_1961_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1960_, v___y_1943_, v___y_1945_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1962_, lean_object* v_impName_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1962_, v_impName_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v___y_1966_);
lean_dec_ref(v___y_1965_);
lean_dec_ref(v___y_1964_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_){
_start:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v_toApplicative_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2042_; 
v___x_1978_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1979_ = l_ReaderT_instMonad___redArg(v___x_1978_);
v_toApplicative_1980_ = lean_ctor_get(v___x_1979_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___x_1979_, 1);
lean_dec(v_unused_2043_);
v___x_1982_ = v___x_1979_;
v_isShared_1983_ = v_isSharedCheck_2042_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_toApplicative_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2042_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v_toFunctor_1984_; lean_object* v_toSeq_1985_; lean_object* v_toSeqLeft_1986_; lean_object* v_toSeqRight_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2040_; 
v_toFunctor_1984_ = lean_ctor_get(v_toApplicative_1980_, 0);
v_toSeq_1985_ = lean_ctor_get(v_toApplicative_1980_, 2);
v_toSeqLeft_1986_ = lean_ctor_get(v_toApplicative_1980_, 3);
v_toSeqRight_1987_ = lean_ctor_get(v_toApplicative_1980_, 4);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_toApplicative_1980_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v_toApplicative_1980_, 1);
lean_dec(v_unused_2041_);
v___x_1989_ = v_toApplicative_1980_;
v_isShared_1990_ = v_isSharedCheck_2040_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_toSeqRight_1987_);
lean_inc(v_toSeqLeft_1986_);
lean_inc(v_toSeq_1985_);
lean_inc(v_toFunctor_1984_);
lean_dec(v_toApplicative_1980_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2040_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___f_1991_; lean_object* v___f_1992_; lean_object* v___f_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; lean_object* v___f_1996_; lean_object* v___f_1997_; lean_object* v___f_1998_; lean_object* v___x_2000_; 
v___f_1991_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1992_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1984_);
v___f_1993_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1993_, 0, v_toFunctor_1984_);
v___f_1994_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1994_, 0, v_toFunctor_1984_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___f_1993_);
lean_ctor_set(v___x_1995_, 1, v___f_1994_);
v___f_1996_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1996_, 0, v_toSeqRight_1987_);
v___f_1997_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1997_, 0, v_toSeqLeft_1986_);
v___f_1998_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1998_, 0, v_toSeq_1985_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 4, v___f_1996_);
lean_ctor_set(v___x_1989_, 3, v___f_1997_);
lean_ctor_set(v___x_1989_, 2, v___f_1998_);
lean_ctor_set(v___x_1989_, 1, v___f_1991_);
lean_ctor_set(v___x_1989_, 0, v___x_1995_);
v___x_2000_ = v___x_1989_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_1995_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___f_1991_);
lean_ctor_set(v_reuseFailAlloc_2039_, 2, v___f_1998_);
lean_ctor_set(v_reuseFailAlloc_2039_, 3, v___f_1997_);
lean_ctor_set(v_reuseFailAlloc_2039_, 4, v___f_1996_);
v___x_2000_ = v_reuseFailAlloc_2039_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v___f_1992_);
lean_ctor_set(v___x_1982_, 0, v___x_2000_);
v___x_2002_ = v___x_1982_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___f_1992_);
v___x_2002_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2003_; lean_object* v_toApplicative_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2036_; 
v___x_2003_ = l_ReaderT_instMonad___redArg(v___x_2002_);
v_toApplicative_2004_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v___x_2003_, 1);
lean_dec(v_unused_2037_);
v___x_2006_ = v___x_2003_;
v_isShared_2007_ = v_isSharedCheck_2036_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_toApplicative_2004_);
lean_dec(v___x_2003_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2036_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v_toFunctor_2008_; lean_object* v_toSeq_2009_; lean_object* v_toSeqLeft_2010_; lean_object* v_toSeqRight_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2034_; 
v_toFunctor_2008_ = lean_ctor_get(v_toApplicative_2004_, 0);
v_toSeq_2009_ = lean_ctor_get(v_toApplicative_2004_, 2);
v_toSeqLeft_2010_ = lean_ctor_get(v_toApplicative_2004_, 3);
v_toSeqRight_2011_ = lean_ctor_get(v_toApplicative_2004_, 4);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_toApplicative_2004_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_toApplicative_2004_, 1);
lean_dec(v_unused_2035_);
v___x_2013_ = v_toApplicative_2004_;
v_isShared_2014_ = v_isSharedCheck_2034_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_toSeqRight_2011_);
lean_inc(v_toSeqLeft_2010_);
lean_inc(v_toSeq_2009_);
lean_inc(v_toFunctor_2008_);
lean_dec(v_toApplicative_2004_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2034_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v___f_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___f_2020_; lean_object* v___f_2021_; lean_object* v___f_2022_; lean_object* v___x_2024_; 
v___f_2015_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2016_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_2008_);
v___f_2017_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2017_, 0, v_toFunctor_2008_);
v___f_2018_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2018_, 0, v_toFunctor_2008_);
v___x_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2019_, 0, v___f_2017_);
lean_ctor_set(v___x_2019_, 1, v___f_2018_);
v___f_2020_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2020_, 0, v_toSeqRight_2011_);
v___f_2021_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2021_, 0, v_toSeqLeft_2010_);
v___f_2022_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2022_, 0, v_toSeq_2009_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 4, v___f_2020_);
lean_ctor_set(v___x_2013_, 3, v___f_2021_);
lean_ctor_set(v___x_2013_, 2, v___f_2022_);
lean_ctor_set(v___x_2013_, 1, v___f_2015_);
lean_ctor_set(v___x_2013_, 0, v___x_2019_);
v___x_2024_ = v___x_2013_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___f_2015_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v___f_2022_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v___f_2021_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v___f_2020_);
v___x_2024_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2026_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v___f_2016_);
lean_ctor_set(v___x_2006_, 0, v___x_2024_);
v___x_2026_ = v___x_2006_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___f_2016_);
v___x_2026_ = v_reuseFailAlloc_2032_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_11266__overap_2030_; lean_object* v___x_2031_; 
v___x_2027_ = l_ReaderT_instMonad___redArg(v___x_2026_);
v___x_2028_ = lean_box(0);
v___x_2029_ = l_instInhabitedOfMonad___redArg(v___x_2027_, v___x_2028_);
v___x_11266__overap_2030_ = lean_panic_fn(v___x_2029_, v_msg_1971_);
v___x_2031_ = lean_apply_6(v___x_11266__overap_2030_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, lean_box(0));
return v___x_2031_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2044_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_);
return v_res_2051_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2054_ = l_Lean_stringToMessageData(v___x_2053_);
return v___x_2054_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2056_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2057_ = lean_unsigned_to_nat(11u);
v___x_2058_ = lean_unsigned_to_nat(115u);
v___x_2059_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2060_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2061_ = l_mkPanicMessageWithDecl(v___x_2060_, v___x_2059_, v___x_2058_, v___x_2057_, v___x_2056_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
lean_object* v___x_2077_; lean_object* v_env_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2077_ = lean_st_ref_get(v___y_2067_);
v_env_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc_ref(v_env_2078_);
lean_dec(v___x_2077_);
v___x_2079_ = 0;
lean_inc(v_constName_2062_);
v___x_2080_ = l_Lean_Environment_findAsync_x3f(v_env_2078_, v_constName_2062_, v___x_2079_);
if (lean_obj_tag(v___x_2080_) == 1)
{
lean_object* v_val_2081_; uint8_t v_kind_2082_; 
v_val_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_val_2081_);
lean_dec_ref(v___x_2080_);
v_kind_2082_ = lean_ctor_get_uint8(v_val_2081_, sizeof(void*)*3);
if (v_kind_2082_ == 0)
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2081_);
if (lean_obj_tag(v___x_2083_) == 1)
{
lean_object* v_val_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec(v_constName_2062_);
v_val_2084_ = lean_ctor_get(v___x_2083_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2083_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2083_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_val_2084_);
lean_dec(v___x_2083_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
lean_ctor_set_tag(v___x_2086_, 0);
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_val_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref(v___x_2083_);
v___x_2092_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
lean_inc(v___y_2067_);
lean_inc_ref(v___y_2066_);
lean_inc(v___y_2065_);
lean_inc_ref(v___y_2064_);
v___x_2093_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2092_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2102_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2102_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2102_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
if (lean_obj_tag(v_a_2094_) == 0)
{
lean_del_object(v___x_2096_);
goto v___jp_2069_;
}
else
{
lean_object* v_val_2098_; lean_object* v___x_2100_; 
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v_constName_2062_);
v_val_2098_ = lean_ctor_get(v_a_2094_, 0);
lean_inc(v_val_2098_);
lean_dec_ref(v_a_2094_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v_val_2098_);
v___x_2100_ = v___x_2096_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_val_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v_constName_2062_);
v_a_2103_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2093_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2093_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
}
else
{
lean_dec(v_val_2081_);
lean_dec_ref(v___y_2063_);
goto v___jp_2069_;
}
}
else
{
lean_dec(v___x_2080_);
lean_dec_ref(v___y_2063_);
goto v___jp_2069_;
}
v___jp_2069_:
{
lean_object* v___x_2070_; uint8_t v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2070_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2071_ = 0;
v___x_2072_ = l_Lean_MessageData_ofConstName(v_constName_2062_, v___x_2071_);
v___x_2073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2070_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2073_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
v___x_2076_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2075_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v_toInductiveVal_2128_; lean_object* v_toConstantVal_2129_; lean_object* v_lparams_2130_; lean_object* v_params_2131_; lean_object* v_compFieldVars_2132_; lean_object* v_numIndices_2133_; lean_object* v_ctors_2134_; lean_object* v_name_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_toInductiveVal_2128_ = lean_ctor_get(v_a_2122_, 0);
v_toConstantVal_2129_ = lean_ctor_get(v_toInductiveVal_2128_, 0);
v_lparams_2130_ = lean_ctor_get(v_a_2122_, 1);
v_params_2131_ = lean_ctor_get(v_a_2122_, 2);
v_compFieldVars_2132_ = lean_ctor_get(v_a_2122_, 4);
v_numIndices_2133_ = lean_ctor_get(v_toInductiveVal_2128_, 2);
v_ctors_2134_ = lean_ctor_get(v_toInductiveVal_2128_, 4);
v_name_2135_ = lean_ctor_get(v_toConstantVal_2129_, 0);
lean_inc(v_name_2135_);
v___x_2136_ = l_Lean_mkCasesOnName(v_name_2135_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc_ref(v_a_2122_);
lean_inc(v___x_2136_);
v___x_2137_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2136_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2137_);
v___x_2139_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_2135_);
v___x_2140_ = l_Lean_Name_append(v_name_2135_, v___x_2139_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc(v___x_2140_);
v___x_2141_ = l_Lean_mkCasesOn(v___x_2140_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2202_; 
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2202_ == 0)
{
lean_object* v_unused_2203_; 
v_unused_2203_ = lean_ctor_get(v___x_2141_, 0);
lean_dec(v_unused_2203_);
v___x_2143_ = v___x_2141_;
v_isShared_2144_ = v_isSharedCheck_2202_;
goto v_resetjp_2142_;
}
else
{
lean_dec(v___x_2141_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2202_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v_toConstantVal_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2198_; 
v_toConstantVal_2145_ = lean_ctor_get(v_a_2138_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v_a_2138_);
if (v_isSharedCheck_2198_ == 0)
{
lean_object* v_unused_2199_; lean_object* v_unused_2200_; lean_object* v_unused_2201_; 
v_unused_2199_ = lean_ctor_get(v_a_2138_, 3);
lean_dec(v_unused_2199_);
v_unused_2200_ = lean_ctor_get(v_a_2138_, 2);
lean_dec(v_unused_2200_);
v_unused_2201_ = lean_ctor_get(v_a_2138_, 1);
lean_dec(v_unused_2201_);
v___x_2147_ = v_a_2138_;
v_isShared_2148_ = v_isSharedCheck_2198_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_toConstantVal_2145_);
lean_dec(v_a_2138_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2198_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v_levelParams_2149_; lean_object* v_type_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2196_; 
v_levelParams_2149_ = lean_ctor_get(v_toConstantVal_2145_, 1);
v_type_2150_ = lean_ctor_get(v_toConstantVal_2145_, 2);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_toConstantVal_2145_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v_toConstantVal_2145_, 0);
lean_dec(v_unused_2197_);
v___x_2152_ = v_toConstantVal_2145_;
v_isShared_2153_ = v_isSharedCheck_2196_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_type_2150_);
lean_inc(v_levelParams_2149_);
lean_dec(v_toConstantVal_2145_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2196_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2154_; 
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc_ref(v_type_2150_);
v___x_2154_ = l_Lean_Meta_instantiateForall(v_type_2150_, v_params_2131_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2154_) == 0)
{
lean_object* v_a_2155_; lean_object* v___x_2156_; lean_object* v___f_2157_; uint8_t v___x_2158_; lean_object* v___x_2159_; 
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v___x_2156_ = l_Lean_instInhabitedExpr;
lean_inc(v_levelParams_2149_);
lean_inc_ref(v_compFieldVars_2132_);
lean_inc(v_ctors_2134_);
lean_inc_ref(v_params_2131_);
lean_inc(v_lparams_2130_);
lean_inc(v_numIndices_2133_);
v___f_2157_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2157_, 0, v_numIndices_2133_);
lean_closure_set(v___f_2157_, 1, v___x_2156_);
lean_closure_set(v___f_2157_, 2, v___x_2140_);
lean_closure_set(v___f_2157_, 3, v_lparams_2130_);
lean_closure_set(v___f_2157_, 4, v_params_2131_);
lean_closure_set(v___f_2157_, 5, v_ctors_2134_);
lean_closure_set(v___f_2157_, 6, v_compFieldVars_2132_);
lean_closure_set(v___f_2157_, 7, v_levelParams_2149_);
v___x_2158_ = 0;
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
lean_inc(v_a_2124_);
lean_inc_ref(v_a_2123_);
lean_inc_ref(v_a_2122_);
v___x_2159_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2155_, v___f_2157_, v___x_2158_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2136_);
v___x_2162_ = l_Lean_Name_append(v___x_2136_, v___x_2161_);
lean_inc(v___x_2162_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2162_);
v___x_2164_ = v___x_2152_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v___x_2162_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_levelParams_2149_);
lean_ctor_set(v_reuseFailAlloc_2179_, 2, v_type_2150_);
v___x_2164_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2165_; uint8_t v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2165_ = lean_box(0);
v___x_2166_ = 0;
v___x_2167_ = lean_box(0);
lean_inc(v___x_2162_);
v___x_2168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2162_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 3, v___x_2168_);
lean_ctor_set(v___x_2147_, 2, v___x_2165_);
lean_ctor_set(v___x_2147_, 1, v_a_2160_);
lean_ctor_set(v___x_2147_, 0, v___x_2164_);
v___x_2170_ = v___x_2147_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v___x_2164_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_a_2160_);
lean_ctor_set(v_reuseFailAlloc_2178_, 2, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2178_, 3, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
lean_ctor_set_uint8(v___x_2170_, sizeof(void*)*4, v___x_2166_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 1);
lean_ctor_set(v___x_2143_, 0, v___x_2170_);
v___x_2172_ = v___x_2143_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; 
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
v___x_2173_ = l_Lean_addDecl(v___x_2172_, v___x_2158_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2173_) == 0)
{
uint8_t v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v___x_2173_);
v___x_2174_ = 0;
lean_inc(v___x_2162_);
v___x_2175_ = l_Lean_Meta_setInlineAttribute(v___x_2162_, v___x_2174_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v___x_2176_; 
lean_dec_ref(v___x_2175_);
v___x_2176_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2136_, v___x_2162_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_a_2122_);
return v___x_2176_;
}
else
{
lean_dec(v___x_2162_);
lean_dec(v___x_2136_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_a_2122_);
return v___x_2175_;
}
}
else
{
lean_dec(v___x_2162_);
lean_dec(v___x_2136_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_a_2122_);
return v___x_2173_;
}
}
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2187_; 
lean_del_object(v___x_2152_);
lean_dec_ref(v_type_2150_);
lean_dec(v_levelParams_2149_);
lean_del_object(v___x_2147_);
lean_del_object(v___x_2143_);
lean_dec(v___x_2136_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_a_2122_);
v_a_2180_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2182_ = v___x_2159_;
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2159_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2187_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_a_2180_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
else
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2195_; 
lean_del_object(v___x_2152_);
lean_dec_ref(v_type_2150_);
lean_dec(v_levelParams_2149_);
lean_del_object(v___x_2147_);
lean_del_object(v___x_2143_);
lean_dec(v___x_2140_);
lean_dec(v___x_2136_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_a_2122_);
v_a_2188_ = lean_ctor_get(v___x_2154_, 0);
v_isSharedCheck_2195_ = !lean_is_exclusive(v___x_2154_);
if (v_isSharedCheck_2195_ == 0)
{
v___x_2190_ = v___x_2154_;
v_isShared_2191_ = v_isSharedCheck_2195_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2154_);
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
}
}
else
{
lean_dec(v___x_2140_);
lean_dec(v_a_2138_);
lean_dec(v___x_2136_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_a_2122_);
return v___x_2141_;
}
}
else
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2211_; 
lean_dec(v___x_2136_);
lean_dec(v_a_2126_);
lean_dec_ref(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_a_2122_);
v_a_2204_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2206_ = v___x_2137_;
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2137_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2211_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2209_; 
if (v_isShared_2207_ == 0)
{
v___x_2209_ = v___x_2206_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_a_2204_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_, lean_object* v_a_2215_, lean_object* v_a_2216_, lean_object* v_a_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2212_, v_a_2213_, v_a_2214_, v_a_2215_, v_a_2216_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2219_, lean_object* v_R_2220_, lean_object* v_a_2221_, lean_object* v_b_2222_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2221_, v_b_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2224_, lean_object* v_name_2225_, uint8_t v_bi_2226_, lean_object* v_type_2227_, lean_object* v_k_2228_, uint8_t v_kind_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v___x_2236_; 
v___x_2236_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2225_, v_bi_2226_, v_type_2227_, v_k_2228_, v_kind_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2237_, lean_object* v_name_2238_, lean_object* v_bi_2239_, lean_object* v_type_2240_, lean_object* v_k_2241_, lean_object* v_kind_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
uint8_t v_bi_boxed_2249_; uint8_t v_kind_boxed_2250_; lean_object* v_res_2251_; 
v_bi_boxed_2249_ = lean_unbox(v_bi_2239_);
v_kind_boxed_2250_ = lean_unbox(v_kind_2242_);
v_res_2251_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2237_, v_name_2238_, v_bi_boxed_2249_, v_type_2240_, v_k_2241_, v_kind_boxed_2250_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2252_, lean_object* v_name_2253_, lean_object* v_type_2254_, lean_object* v_k_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; 
v___x_2262_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2253_, v_type_2254_, v_k_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2263_, lean_object* v_name_2264_, lean_object* v_type_2265_, lean_object* v_k_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2263_, v_name_2264_, v_type_2265_, v_k_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2274_, v___y_2277_, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec_ref(v___y_2283_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2290_, size_t v_sz_2291_, size_t v_i_2292_, lean_object* v_bs_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
uint8_t v___x_2299_; 
v___x_2299_ = lean_usize_dec_lt(v_i_2292_, v_sz_2291_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; 
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v___x_2290_);
v___x_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_bs_2293_);
return v___x_2300_;
}
else
{
lean_object* v_v_2301_; lean_object* v___x_2302_; 
v_v_2301_ = lean_array_uget_borrowed(v_bs_2293_, v_i_2292_);
lean_inc(v___y_2297_);
lean_inc_ref(v___y_2296_);
lean_inc(v___y_2295_);
lean_inc_ref(v___y_2294_);
lean_inc_ref(v___x_2290_);
lean_inc(v_v_2301_);
v___x_2302_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2301_, v___x_2290_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; lean_object* v___x_2304_; lean_object* v_bs_x27_2305_; size_t v___x_2306_; size_t v___x_2307_; lean_object* v___x_2308_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v___x_2304_ = lean_unsigned_to_nat(0u);
v_bs_x27_2305_ = lean_array_uset(v_bs_2293_, v_i_2292_, v___x_2304_);
v___x_2306_ = ((size_t)1ULL);
v___x_2307_ = lean_usize_add(v_i_2292_, v___x_2306_);
v___x_2308_ = lean_array_uset(v_bs_x27_2305_, v_i_2292_, v_a_2303_);
v_i_2292_ = v___x_2307_;
v_bs_2293_ = v___x_2308_;
goto _start;
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec_ref(v_bs_2293_);
lean_dec_ref(v___x_2290_);
v_a_2310_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2302_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2302_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2318_, lean_object* v_sz_2319_, lean_object* v_i_2320_, lean_object* v_bs_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
size_t v_sz_boxed_2327_; size_t v_i_boxed_2328_; lean_object* v_res_2329_; 
v_sz_boxed_2327_ = lean_unbox_usize(v_sz_2319_);
lean_dec(v_sz_2319_);
v_i_boxed_2328_ = lean_unbox_usize(v_i_2320_);
lean_dec(v_i_2320_);
v_res_2329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2318_, v_sz_boxed_2327_, v_i_boxed_2328_, v_bs_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2330_, lean_object* v_compFields_2331_, lean_object* v___x_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
v___x_2339_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2330_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2352_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2352_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2352_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
uint8_t v___x_2344_; 
v___x_2344_ = lean_unbox(v_a_2340_);
lean_dec(v_a_2340_);
if (v___x_2344_ == 0)
{
size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
lean_del_object(v___x_2342_);
v_sz_2345_ = lean_array_size(v_compFields_2331_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2332_, v_sz_2345_, v___x_2346_, v_compFields_2331_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
return v___x_2347_;
}
else
{
lean_object* v___x_2348_; lean_object* v___x_2350_; 
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec_ref(v___x_2332_);
lean_dec_ref(v_compFields_2331_);
v___x_2348_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2348_);
v___x_2350_ = v___x_2342_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec_ref(v___x_2332_);
lean_dec_ref(v_compFields_2331_);
v_a_2353_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2339_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2339_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2361_, lean_object* v_compFields_2362_, lean_object* v___x_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2361_, v_compFields_2362_, v___x_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
lean_dec_ref(v___y_2364_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2371_, uint8_t v_isExporting_2372_, lean_object* v___x_2373_, lean_object* v___y_2374_, lean_object* v___x_2375_, lean_object* v_a_x3f_2376_){
_start:
{
lean_object* v___x_2378_; lean_object* v_env_2379_; lean_object* v_nextMacroScope_2380_; lean_object* v_ngen_2381_; lean_object* v_auxDeclNGen_2382_; lean_object* v_traceState_2383_; lean_object* v_messages_2384_; lean_object* v_infoState_2385_; lean_object* v_snapshotTasks_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2411_; 
v___x_2378_ = lean_st_ref_take(v___y_2371_);
v_env_2379_ = lean_ctor_get(v___x_2378_, 0);
v_nextMacroScope_2380_ = lean_ctor_get(v___x_2378_, 1);
v_ngen_2381_ = lean_ctor_get(v___x_2378_, 2);
v_auxDeclNGen_2382_ = lean_ctor_get(v___x_2378_, 3);
v_traceState_2383_ = lean_ctor_get(v___x_2378_, 4);
v_messages_2384_ = lean_ctor_get(v___x_2378_, 6);
v_infoState_2385_ = lean_ctor_get(v___x_2378_, 7);
v_snapshotTasks_2386_ = lean_ctor_get(v___x_2378_, 8);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2411_ == 0)
{
lean_object* v_unused_2412_; 
v_unused_2412_ = lean_ctor_get(v___x_2378_, 5);
lean_dec(v_unused_2412_);
v___x_2388_ = v___x_2378_;
v_isShared_2389_ = v_isSharedCheck_2411_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_snapshotTasks_2386_);
lean_inc(v_infoState_2385_);
lean_inc(v_messages_2384_);
lean_inc(v_traceState_2383_);
lean_inc(v_auxDeclNGen_2382_);
lean_inc(v_ngen_2381_);
lean_inc(v_nextMacroScope_2380_);
lean_inc(v_env_2379_);
lean_dec(v___x_2378_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2411_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2390_ = l_Lean_Environment_setExporting(v_env_2379_, v_isExporting_2372_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 5, v___x_2373_);
lean_ctor_set(v___x_2388_, 0, v___x_2390_);
v___x_2392_ = v___x_2388_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2410_, 1, v_nextMacroScope_2380_);
lean_ctor_set(v_reuseFailAlloc_2410_, 2, v_ngen_2381_);
lean_ctor_set(v_reuseFailAlloc_2410_, 3, v_auxDeclNGen_2382_);
lean_ctor_set(v_reuseFailAlloc_2410_, 4, v_traceState_2383_);
lean_ctor_set(v_reuseFailAlloc_2410_, 5, v___x_2373_);
lean_ctor_set(v_reuseFailAlloc_2410_, 6, v_messages_2384_);
lean_ctor_set(v_reuseFailAlloc_2410_, 7, v_infoState_2385_);
lean_ctor_set(v_reuseFailAlloc_2410_, 8, v_snapshotTasks_2386_);
v___x_2392_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v_mctx_2395_; lean_object* v_zetaDeltaFVarIds_2396_; lean_object* v_postponed_2397_; lean_object* v_diag_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2408_; 
v___x_2393_ = lean_st_ref_set(v___y_2371_, v___x_2392_);
v___x_2394_ = lean_st_ref_take(v___y_2374_);
v_mctx_2395_ = lean_ctor_get(v___x_2394_, 0);
v_zetaDeltaFVarIds_2396_ = lean_ctor_get(v___x_2394_, 2);
v_postponed_2397_ = lean_ctor_get(v___x_2394_, 3);
v_diag_2398_ = lean_ctor_get(v___x_2394_, 4);
v_isSharedCheck_2408_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2408_ == 0)
{
lean_object* v_unused_2409_; 
v_unused_2409_ = lean_ctor_get(v___x_2394_, 1);
lean_dec(v_unused_2409_);
v___x_2400_ = v___x_2394_;
v_isShared_2401_ = v_isSharedCheck_2408_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_diag_2398_);
lean_inc(v_postponed_2397_);
lean_inc(v_zetaDeltaFVarIds_2396_);
lean_inc(v_mctx_2395_);
lean_dec(v___x_2394_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2408_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
lean_object* v___x_2403_; 
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 1, v___x_2375_);
v___x_2403_ = v___x_2400_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v_mctx_2395_);
lean_ctor_set(v_reuseFailAlloc_2407_, 1, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2407_, 2, v_zetaDeltaFVarIds_2396_);
lean_ctor_set(v_reuseFailAlloc_2407_, 3, v_postponed_2397_);
lean_ctor_set(v_reuseFailAlloc_2407_, 4, v_diag_2398_);
v___x_2403_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = lean_st_ref_set(v___y_2374_, v___x_2403_);
v___x_2405_ = lean_box(0);
v___x_2406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
return v___x_2406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2413_, lean_object* v_isExporting_2414_, lean_object* v___x_2415_, lean_object* v___y_2416_, lean_object* v___x_2417_, lean_object* v_a_x3f_2418_, lean_object* v___y_2419_){
_start:
{
uint8_t v_isExporting_boxed_2420_; lean_object* v_res_2421_; 
v_isExporting_boxed_2420_ = lean_unbox(v_isExporting_2414_);
v_res_2421_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2413_, v_isExporting_boxed_2420_, v___x_2415_, v___y_2416_, v___x_2417_, v_a_x3f_2418_);
lean_dec(v_a_x3f_2418_);
lean_dec(v___y_2416_);
lean_dec(v___y_2413_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2422_, uint8_t v_isExporting_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v_env_2431_; uint8_t v_isExporting_2432_; lean_object* v___x_2433_; lean_object* v_env_2434_; lean_object* v_nextMacroScope_2435_; lean_object* v_ngen_2436_; lean_object* v_auxDeclNGen_2437_; lean_object* v_traceState_2438_; lean_object* v_messages_2439_; lean_object* v_infoState_2440_; lean_object* v_snapshotTasks_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2495_; 
v___x_2430_ = lean_st_ref_get(v___y_2428_);
v_env_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc_ref(v_env_2431_);
lean_dec(v___x_2430_);
v_isExporting_2432_ = lean_ctor_get_uint8(v_env_2431_, sizeof(void*)*8);
lean_dec_ref(v_env_2431_);
v___x_2433_ = lean_st_ref_take(v___y_2428_);
v_env_2434_ = lean_ctor_get(v___x_2433_, 0);
v_nextMacroScope_2435_ = lean_ctor_get(v___x_2433_, 1);
v_ngen_2436_ = lean_ctor_get(v___x_2433_, 2);
v_auxDeclNGen_2437_ = lean_ctor_get(v___x_2433_, 3);
v_traceState_2438_ = lean_ctor_get(v___x_2433_, 4);
v_messages_2439_ = lean_ctor_get(v___x_2433_, 6);
v_infoState_2440_ = lean_ctor_get(v___x_2433_, 7);
v_snapshotTasks_2441_ = lean_ctor_get(v___x_2433_, 8);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2495_ == 0)
{
lean_object* v_unused_2496_; 
v_unused_2496_ = lean_ctor_get(v___x_2433_, 5);
lean_dec(v_unused_2496_);
v___x_2443_ = v___x_2433_;
v_isShared_2444_ = v_isSharedCheck_2495_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_snapshotTasks_2441_);
lean_inc(v_infoState_2440_);
lean_inc(v_messages_2439_);
lean_inc(v_traceState_2438_);
lean_inc(v_auxDeclNGen_2437_);
lean_inc(v_ngen_2436_);
lean_inc(v_nextMacroScope_2435_);
lean_inc(v_env_2434_);
lean_dec(v___x_2433_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2495_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2445_ = l_Lean_Environment_setExporting(v_env_2434_, v_isExporting_2423_);
v___x_2446_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 5, v___x_2446_);
lean_ctor_set(v___x_2443_, 0, v___x_2445_);
v___x_2448_ = v___x_2443_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_nextMacroScope_2435_);
lean_ctor_set(v_reuseFailAlloc_2494_, 2, v_ngen_2436_);
lean_ctor_set(v_reuseFailAlloc_2494_, 3, v_auxDeclNGen_2437_);
lean_ctor_set(v_reuseFailAlloc_2494_, 4, v_traceState_2438_);
lean_ctor_set(v_reuseFailAlloc_2494_, 5, v___x_2446_);
lean_ctor_set(v_reuseFailAlloc_2494_, 6, v_messages_2439_);
lean_ctor_set(v_reuseFailAlloc_2494_, 7, v_infoState_2440_);
lean_ctor_set(v_reuseFailAlloc_2494_, 8, v_snapshotTasks_2441_);
v___x_2448_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v_mctx_2451_; lean_object* v_zetaDeltaFVarIds_2452_; lean_object* v_postponed_2453_; lean_object* v_diag_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2492_; 
v___x_2449_ = lean_st_ref_set(v___y_2428_, v___x_2448_);
v___x_2450_ = lean_st_ref_take(v___y_2426_);
v_mctx_2451_ = lean_ctor_get(v___x_2450_, 0);
v_zetaDeltaFVarIds_2452_ = lean_ctor_get(v___x_2450_, 2);
v_postponed_2453_ = lean_ctor_get(v___x_2450_, 3);
v_diag_2454_ = lean_ctor_get(v___x_2450_, 4);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2492_ == 0)
{
lean_object* v_unused_2493_; 
v_unused_2493_ = lean_ctor_get(v___x_2450_, 1);
lean_dec(v_unused_2493_);
v___x_2456_ = v___x_2450_;
v_isShared_2457_ = v_isSharedCheck_2492_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_diag_2454_);
lean_inc(v_postponed_2453_);
lean_inc(v_zetaDeltaFVarIds_2452_);
lean_inc(v_mctx_2451_);
lean_dec(v___x_2450_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2492_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2458_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 1, v___x_2458_);
v___x_2460_ = v___x_2456_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_mctx_2451_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_zetaDeltaFVarIds_2452_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_postponed_2453_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v_diag_2454_);
v___x_2460_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2461_; lean_object* v_r_2462_; 
v___x_2461_ = lean_st_ref_set(v___y_2426_, v___x_2460_);
lean_inc(v___y_2428_);
lean_inc(v___y_2426_);
v_r_2462_ = lean_apply_6(v_x_2422_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, lean_box(0));
if (lean_obj_tag(v_r_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2479_; 
v_a_2463_ = lean_ctor_get(v_r_2462_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_r_2462_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2465_ = v_r_2462_;
v_isShared_2466_ = v_isSharedCheck_2479_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v_r_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2479_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
lean_inc(v_a_2463_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set_tag(v___x_2465_, 1);
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
v___x_2469_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2428_, v_isExporting_2432_, v___x_2446_, v___y_2426_, v___x_2458_, v___x_2468_);
lean_dec_ref(v___x_2468_);
lean_dec(v___y_2426_);
lean_dec(v___y_2428_);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2476_ == 0)
{
lean_object* v_unused_2477_; 
v_unused_2477_ = lean_ctor_get(v___x_2469_, 0);
lean_dec(v_unused_2477_);
v___x_2471_ = v___x_2469_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_dec(v___x_2469_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 0, v_a_2463_);
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2463_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2489_; 
v_a_2480_ = lean_ctor_get(v_r_2462_, 0);
lean_inc(v_a_2480_);
lean_dec_ref(v_r_2462_);
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2428_, v_isExporting_2432_, v___x_2446_, v___y_2426_, v___x_2458_, v___x_2481_);
lean_dec(v___y_2426_);
lean_dec(v___y_2428_);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v___x_2482_, 0);
lean_dec(v_unused_2490_);
v___x_2484_ = v___x_2482_;
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
else
{
lean_dec(v___x_2482_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2489_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2487_; 
if (v_isShared_2485_ == 0)
{
lean_ctor_set_tag(v___x_2484_, 1);
lean_ctor_set(v___x_2484_, 0, v_a_2480_);
v___x_2487_ = v___x_2484_;
goto v_reusejp_2486_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v_a_2480_);
v___x_2487_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2486_;
}
v_reusejp_2486_:
{
return v___x_2487_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_x_2497_, lean_object* v_isExporting_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_){
_start:
{
uint8_t v_isExporting_boxed_2505_; lean_object* v_res_2506_; 
v_isExporting_boxed_2505_ = lean_unbox(v_isExporting_2498_);
v_res_2506_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2497_, v_isExporting_boxed_2505_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(lean_object* v_x_2507_, uint8_t v_when_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
if (v_when_2508_ == 0)
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_apply_6(v_x_2507_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, lean_box(0));
return v___x_2515_;
}
else
{
uint8_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = 0;
v___x_2517_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2507_, v___x_2516_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg___boxed(lean_object* v_x_2518_, lean_object* v_when_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
uint8_t v_when_boxed_2526_; lean_object* v_res_2527_; 
v_when_boxed_2526_ = lean_unbox(v_when_2519_);
v_res_2527_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2518_, v_when_boxed_2526_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(lean_object* v_params_2528_, lean_object* v___x_2529_, lean_object* v_head_2530_, lean_object* v_compFields_2531_, lean_object* v_lparams_2532_, lean_object* v_levelParams_2533_, lean_object* v___x_2534_, lean_object* v_fields_2535_, lean_object* v_retTy_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___f_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; 
lean_inc_ref(v_params_2528_);
v___x_2543_ = l_Array_append___redArg(v_params_2528_, v_fields_2535_);
lean_inc_ref(v___x_2529_);
v___x_2544_ = l_Lean_mkAppN(v___x_2529_, v___x_2543_);
lean_inc(v_head_2530_);
v___f_2545_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_2545_, 0, v_head_2530_);
lean_closure_set(v___f_2545_, 1, v_compFields_2531_);
lean_closure_set(v___f_2545_, 2, v___x_2544_);
v___x_2546_ = 1;
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2538_);
lean_inc_ref(v___y_2537_);
v___x_2547_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___f_2545_, v___x_2546_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2549_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v___x_2547_);
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2538_);
v___x_2549_ = lean_infer_type(v___x_2529_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref(v___x_2549_);
v___x_2551_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_head_2530_);
v___x_2552_ = l_Lean_Name_append(v_head_2530_, v___x_2551_);
v___x_2553_ = l_Lean_mkConst(v___x_2552_, v_lparams_2532_);
v___x_2554_ = l_Array_append___redArg(v_params_2528_, v_a_2548_);
lean_dec(v_a_2548_);
v___x_2555_ = l_Array_append___redArg(v___x_2554_, v_fields_2535_);
v___x_2556_ = l_Lean_mkAppN(v___x_2553_, v___x_2555_);
lean_dec_ref(v___x_2555_);
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2538_);
v___x_2557_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_retTy_2536_, v___x_2556_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v_a_2558_; uint8_t v___x_2559_; uint8_t v___x_2560_; lean_object* v___x_2561_; 
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
lean_inc(v_a_2558_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = 0;
v___x_2560_ = 1;
v___x_2561_ = l_Lean_Meta_mkLambdaFVars(v___x_2543_, v_a_2558_, v___x_2559_, v___x_2546_, v___x_2559_, v___x_2546_, v___x_2560_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec_ref(v___x_2543_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref(v___x_2561_);
v___x_2563_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2530_);
v___x_2564_ = l_Lean_Name_append(v_head_2530_, v___x_2563_);
lean_inc(v___x_2564_);
v___x_2565_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2565_, 0, v___x_2564_);
lean_ctor_set(v___x_2565_, 1, v_levelParams_2533_);
lean_ctor_set(v___x_2565_, 2, v_a_2550_);
v___x_2566_ = lean_box(0);
v___x_2567_ = 0;
v___x_2568_ = lean_box(0);
lean_inc(v___x_2564_);
v___x_2569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2564_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_2570_, 0, v___x_2565_);
lean_ctor_set(v___x_2570_, 1, v_a_2562_);
lean_ctor_set(v___x_2570_, 2, v___x_2566_);
lean_ctor_set(v___x_2570_, 3, v___x_2569_);
lean_ctor_set_uint8(v___x_2570_, sizeof(void*)*4, v___x_2567_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
v___x_2572_ = l_Lean_addDecl(v___x_2571_, v___x_2559_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref(v___x_2572_);
lean_inc(v___x_2564_);
lean_inc(v_head_2530_);
v___x_2573_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2530_, v___x_2564_, v___y_2537_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec_ref(v___y_2537_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v___x_2574_; 
lean_dec_ref(v___x_2573_);
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
v___x_2574_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2530_, v___y_2540_, v___y_2541_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2585_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2577_ = v___x_2574_;
v_isShared_2578_ = v_isSharedCheck_2585_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2585_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
uint8_t v___x_2579_; 
v___x_2579_ = lean_unbox(v_a_2575_);
lean_dec(v_a_2575_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2581_; 
lean_dec(v___x_2564_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2534_);
v___x_2581_ = v___x_2577_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2534_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
else
{
uint8_t v___x_2583_; lean_object* v___x_2584_; 
lean_del_object(v___x_2577_);
v___x_2583_ = 0;
v___x_2584_ = l_Lean_Meta_setInlineAttribute(v___x_2564_, v___x_2583_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
return v___x_2584_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v___x_2564_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
v_a_2586_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2574_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2574_);
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
lean_dec(v___x_2564_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec(v_head_2530_);
return v___x_2573_;
}
}
else
{
lean_dec(v___x_2564_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v_head_2530_);
return v___x_2572_;
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_a_2550_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v_levelParams_2533_);
lean_dec(v_head_2530_);
v_a_2594_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2561_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2561_);
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
lean_dec(v_a_2550_);
lean_dec_ref(v___x_2543_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec(v_levelParams_2533_);
lean_dec(v_head_2530_);
v_a_2602_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2604_ = v___x_2557_;
v_isShared_2605_ = v_isSharedCheck_2609_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2557_);
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
lean_dec(v_a_2548_);
lean_dec_ref(v___x_2543_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec_ref(v_retTy_2536_);
lean_dec(v_levelParams_2533_);
lean_dec(v_lparams_2532_);
lean_dec(v_head_2530_);
lean_dec_ref(v_params_2528_);
v_a_2610_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2549_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2549_);
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
else
{
lean_object* v_a_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2625_; 
lean_dec_ref(v___x_2543_);
lean_dec(v___y_2541_);
lean_dec_ref(v___y_2540_);
lean_dec(v___y_2539_);
lean_dec_ref(v___y_2538_);
lean_dec_ref(v___y_2537_);
lean_dec_ref(v_retTy_2536_);
lean_dec(v_levelParams_2533_);
lean_dec(v_lparams_2532_);
lean_dec(v_head_2530_);
lean_dec_ref(v___x_2529_);
lean_dec_ref(v_params_2528_);
v_a_2618_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2620_ = v___x_2547_;
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_a_2618_);
lean_dec(v___x_2547_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2625_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed(lean_object* v_params_2626_, lean_object* v___x_2627_, lean_object* v_head_2628_, lean_object* v_compFields_2629_, lean_object* v_lparams_2630_, lean_object* v_levelParams_2631_, lean_object* v___x_2632_, lean_object* v_fields_2633_, lean_object* v_retTy_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1(v_params_2626_, v___x_2627_, v_head_2628_, v_compFields_2629_, v_lparams_2630_, v_levelParams_2631_, v___x_2632_, v_fields_2633_, v_retTy_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_);
lean_dec_ref(v_fields_2633_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(lean_object* v_lparams_2642_, lean_object* v_params_2643_, lean_object* v_compFields_2644_, lean_object* v_levelParams_2645_, lean_object* v_as_x27_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
if (lean_obj_tag(v_as_x27_2646_) == 0)
{
lean_object* v___x_2654_; 
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v_levelParams_2645_);
lean_dec_ref(v_compFields_2644_);
lean_dec_ref(v_params_2643_);
lean_dec(v_lparams_2642_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_b_2647_);
return v___x_2654_;
}
else
{
lean_object* v_head_2655_; lean_object* v_tail_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v_head_2655_ = lean_ctor_get(v_as_x27_2646_, 0);
lean_inc(v_head_2655_);
v_tail_2656_ = lean_ctor_get(v_as_x27_2646_, 1);
lean_inc(v_tail_2656_);
lean_dec_ref(v_as_x27_2646_);
lean_inc(v_lparams_2642_);
lean_inc(v_head_2655_);
v___x_2657_ = l_Lean_mkConst(v_head_2655_, v_lparams_2642_);
lean_inc_ref(v___x_2657_);
v___x_2658_ = l_Lean_mkAppN(v___x_2657_, v_params_2643_);
lean_inc(v___y_2652_);
lean_inc_ref(v___y_2651_);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
v___x_2659_ = lean_infer_type(v___x_2658_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; lean_object* v___f_2662_; uint8_t v___x_2663_; lean_object* v___x_2664_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
v___x_2661_ = lean_box(0);
lean_inc(v_levelParams_2645_);
lean_inc(v_lparams_2642_);
lean_inc_ref(v_compFields_2644_);
lean_inc_ref(v_params_2643_);
v___f_2662_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__1___boxed), 15, 7);
lean_closure_set(v___f_2662_, 0, v_params_2643_);
lean_closure_set(v___f_2662_, 1, v___x_2657_);
lean_closure_set(v___f_2662_, 2, v_head_2655_);
lean_closure_set(v___f_2662_, 3, v_compFields_2644_);
lean_closure_set(v___f_2662_, 4, v_lparams_2642_);
lean_closure_set(v___f_2662_, 5, v_levelParams_2645_);
lean_closure_set(v___f_2662_, 6, v___x_2661_);
v___x_2663_ = 0;
lean_inc(v___y_2652_);
lean_inc_ref(v___y_2651_);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2649_);
lean_inc_ref(v___y_2648_);
v___x_2664_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2660_, v___f_2662_, v___x_2663_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_, v___y_2652_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_dec_ref(v___x_2664_);
v_as_x27_2646_ = v_tail_2656_;
v_b_2647_ = v___x_2661_;
goto _start;
}
else
{
lean_dec(v_tail_2656_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v_levelParams_2645_);
lean_dec_ref(v_compFields_2644_);
lean_dec_ref(v_params_2643_);
lean_dec(v_lparams_2642_);
return v___x_2664_;
}
}
else
{
lean_object* v_a_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
lean_dec_ref(v___x_2657_);
lean_dec(v_tail_2656_);
lean_dec(v_head_2655_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
lean_dec(v___y_2650_);
lean_dec_ref(v___y_2649_);
lean_dec_ref(v___y_2648_);
lean_dec(v_levelParams_2645_);
lean_dec_ref(v_compFields_2644_);
lean_dec_ref(v_params_2643_);
lean_dec(v_lparams_2642_);
v_a_2666_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2673_ == 0)
{
v___x_2668_ = v___x_2659_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_a_2666_);
lean_dec(v___x_2659_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___boxed(lean_object* v_lparams_2674_, lean_object* v_params_2675_, lean_object* v_compFields_2676_, lean_object* v_levelParams_2677_, lean_object* v_as_x27_2678_, lean_object* v_b_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2674_, v_params_2675_, v_compFields_2676_, v_levelParams_2677_, v_as_x27_2678_, v_b_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors(lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_toInductiveVal_2693_; lean_object* v_toConstantVal_2694_; lean_object* v_lparams_2695_; lean_object* v_params_2696_; lean_object* v_compFields_2697_; lean_object* v_ctors_2698_; lean_object* v_levelParams_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_toInductiveVal_2693_ = lean_ctor_get(v_a_2687_, 0);
v_toConstantVal_2694_ = lean_ctor_get(v_toInductiveVal_2693_, 0);
v_lparams_2695_ = lean_ctor_get(v_a_2687_, 1);
lean_inc(v_lparams_2695_);
v_params_2696_ = lean_ctor_get(v_a_2687_, 2);
lean_inc_ref(v_params_2696_);
v_compFields_2697_ = lean_ctor_get(v_a_2687_, 3);
lean_inc_ref(v_compFields_2697_);
v_ctors_2698_ = lean_ctor_get(v_toInductiveVal_2693_, 4);
lean_inc(v_ctors_2698_);
v_levelParams_2699_ = lean_ctor_get(v_toConstantVal_2694_, 1);
lean_inc(v_levelParams_2699_);
v___x_2700_ = lean_box(0);
v___x_2701_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2695_, v_params_2696_, v_compFields_2697_, v_levelParams_2699_, v_ctors_2698_, v___x_2700_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2708_ == 0)
{
lean_object* v_unused_2709_; 
v_unused_2709_ = lean_ctor_get(v___x_2701_, 0);
lean_dec(v_unused_2709_);
v___x_2703_ = v___x_2701_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_dec(v___x_2701_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 0, v___x_2700_);
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2700_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
else
{
return v___x_2701_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideConstructors___boxed(lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_Elab_ComputedFields_overrideConstructors(v_a_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(lean_object* v___x_2717_, size_t v_sz_2718_, size_t v_i_2719_, lean_object* v_bs_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2717_, v_sz_2718_, v_i_2719_, v_bs_2720_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___boxed(lean_object* v___x_2728_, lean_object* v_sz_2729_, lean_object* v_i_2730_, lean_object* v_bs_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
size_t v_sz_boxed_2738_; size_t v_i_boxed_2739_; lean_object* v_res_2740_; 
v_sz_boxed_2738_ = lean_unbox_usize(v_sz_2729_);
lean_dec(v_sz_2729_);
v_i_boxed_2739_ = lean_unbox_usize(v_i_2730_);
lean_dec(v_i_2730_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0(v___x_2728_, v_sz_boxed_2738_, v_i_boxed_2739_, v_bs_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec_ref(v___y_2732_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(lean_object* v_00_u03b1_2741_, lean_object* v_x_2742_, uint8_t v_isExporting_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(v_x_2742_, v_isExporting_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___boxed(lean_object* v_00_u03b1_2751_, lean_object* v_x_2752_, lean_object* v_isExporting_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
uint8_t v_isExporting_boxed_2760_; lean_object* v_res_2761_; 
v_isExporting_boxed_2760_ = lean_unbox(v_isExporting_2753_);
v_res_2761_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1(v_00_u03b1_2751_, v_x_2752_, v_isExporting_boxed_2760_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(lean_object* v_00_u03b1_2762_, lean_object* v_x_2763_, uint8_t v_when_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v_x_2763_, v_when_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___boxed(lean_object* v_00_u03b1_2772_, lean_object* v_x_2773_, lean_object* v_when_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
uint8_t v_when_boxed_2781_; lean_object* v_res_2782_; 
v_when_boxed_2781_ = lean_unbox(v_when_2774_);
v_res_2782_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1(v_00_u03b1_2772_, v_x_2773_, v_when_boxed_2781_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(lean_object* v_lparams_2783_, lean_object* v_params_2784_, lean_object* v_compFields_2785_, lean_object* v_levelParams_2786_, lean_object* v_as_2787_, lean_object* v_as_x27_2788_, lean_object* v_b_2789_, lean_object* v_a_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2783_, v_params_2784_, v_compFields_2785_, v_levelParams_2786_, v_as_x27_2788_, v_b_2789_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___boxed(lean_object* v_lparams_2798_, lean_object* v_params_2799_, lean_object* v_compFields_2800_, lean_object* v_levelParams_2801_, lean_object* v_as_2802_, lean_object* v_as_x27_2803_, lean_object* v_b_2804_, lean_object* v_a_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2(v_lparams_2798_, v_params_2799_, v_compFields_2800_, v_levelParams_2801_, v_as_2802_, v_as_x27_2803_, v_b_2804_, v_a_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v_as_2802_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(lean_object* v_v_2813_, lean_object* v_compFieldVars_2814_, lean_object* v___x_2815_, uint8_t v___x_2816_, lean_object* v_params_2817_, lean_object* v___x_2818_, lean_object* v_a_2819_, uint8_t v___x_2820_, lean_object* v_fields_2821_, lean_object* v_x_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
v___x_2829_ = l_Lean_Elab_ComputedFields_isScalarField(v_v_2813_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; uint8_t v___x_2831_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref(v___x_2829_);
v___x_2831_ = lean_unbox(v_a_2830_);
if (v___x_2831_ == 0)
{
lean_object* v___x_2832_; uint8_t v___x_2833_; uint8_t v___x_2834_; uint8_t v___x_2835_; lean_object* v___x_2836_; 
lean_dec(v_a_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v_params_2817_);
v___x_2832_ = l_Array_append___redArg(v_compFieldVars_2814_, v_fields_2821_);
v___x_2833_ = 1;
v___x_2834_ = lean_unbox(v_a_2830_);
v___x_2835_ = lean_unbox(v_a_2830_);
lean_dec(v_a_2830_);
v___x_2836_ = l_Lean_Meta_mkLambdaFVars(v___x_2832_, v___x_2815_, v___x_2834_, v___x_2816_, v___x_2835_, v___x_2816_, v___x_2833_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec_ref(v___x_2832_);
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec(v_a_2830_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v_compFieldVars_2814_);
v___x_2837_ = l_Array_append___redArg(v_params_2817_, v_fields_2821_);
v___x_2838_ = l_Lean_mkAppN(v___x_2818_, v___x_2837_);
lean_dec_ref(v___x_2837_);
lean_inc(v___y_2827_);
lean_inc_ref(v___y_2826_);
lean_inc(v___y_2825_);
lean_inc_ref(v___y_2824_);
v___x_2839_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_a_2819_, v___x_2838_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; uint8_t v___x_2841_; lean_object* v___x_2842_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref(v___x_2839_);
v___x_2841_ = 1;
v___x_2842_ = l_Lean_Meta_mkLambdaFVars(v_fields_2821_, v_a_2840_, v___x_2820_, v___x_2816_, v___x_2820_, v___x_2816_, v___x_2841_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v___x_2842_;
}
else
{
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
return v___x_2839_;
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
lean_dec_ref(v___y_2824_);
lean_dec(v_a_2819_);
lean_dec_ref(v___x_2818_);
lean_dec_ref(v_params_2817_);
lean_dec_ref(v___x_2815_);
lean_dec_ref(v_compFieldVars_2814_);
v_a_2843_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2829_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2829_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed(lean_object* v_v_2851_, lean_object* v_compFieldVars_2852_, lean_object* v___x_2853_, lean_object* v___x_2854_, lean_object* v_params_2855_, lean_object* v___x_2856_, lean_object* v_a_2857_, lean_object* v___x_2858_, lean_object* v_fields_2859_, lean_object* v_x_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_){
_start:
{
uint8_t v___x_14624__boxed_2867_; uint8_t v___x_14627__boxed_2868_; lean_object* v_res_2869_; 
v___x_14624__boxed_2867_ = lean_unbox(v___x_2854_);
v___x_14627__boxed_2868_ = lean_unbox(v___x_2858_);
v_res_2869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2851_, v_compFieldVars_2852_, v___x_2853_, v___x_14624__boxed_2867_, v_params_2855_, v___x_2856_, v_a_2857_, v___x_14627__boxed_2868_, v_fields_2859_, v_x_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_, v___y_2865_);
lean_dec_ref(v___y_2861_);
lean_dec_ref(v_x_2860_);
lean_dec_ref(v_fields_2859_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2870_, lean_object* v_compFieldVars_2871_, lean_object* v___x_2872_, lean_object* v_params_2873_, lean_object* v_a_2874_, uint8_t v___x_2875_, size_t v_sz_2876_, size_t v_i_2877_, lean_object* v_bs_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_){
_start:
{
uint8_t v___x_2885_; 
v___x_2885_ = lean_usize_dec_lt(v_i_2877_, v_sz_2876_);
if (v___x_2885_ == 0)
{
lean_object* v___x_2886_; 
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v_a_2874_);
lean_dec_ref(v_params_2873_);
lean_dec_ref(v___x_2872_);
lean_dec_ref(v_compFieldVars_2871_);
lean_dec(v_lparams_2870_);
v___x_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2886_, 0, v_bs_2878_);
return v___x_2886_;
}
else
{
lean_object* v_v_2887_; lean_object* v___x_2888_; lean_object* v_bs_x27_2889_; lean_object* v___y_2891_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; 
v_v_2887_ = lean_array_uget(v_bs_2878_, v_i_2877_);
v___x_2888_ = lean_unsigned_to_nat(0u);
v_bs_x27_2889_ = lean_array_uset(v_bs_2878_, v_i_2877_, v___x_2888_);
lean_inc(v_lparams_2870_);
lean_inc(v_v_2887_);
v___x_2905_ = l_Lean_mkConst(v_v_2887_, v_lparams_2870_);
lean_inc_ref(v___x_2905_);
v___x_2906_ = l_Lean_mkAppN(v___x_2905_, v_params_2873_);
lean_inc(v___y_2883_);
lean_inc_ref(v___y_2882_);
lean_inc(v___y_2881_);
lean_inc_ref(v___y_2880_);
v___x_2907_ = lean_infer_type(v___x_2906_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___f_2911_; lean_object* v___x_2912_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref(v___x_2907_);
v___x_2909_ = lean_box(v___x_2885_);
v___x_2910_ = lean_box(v___x_2875_);
lean_inc(v_a_2874_);
lean_inc_ref(v_params_2873_);
lean_inc_ref(v___x_2872_);
lean_inc_ref(v_compFieldVars_2871_);
v___f_2911_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2911_, 0, v_v_2887_);
lean_closure_set(v___f_2911_, 1, v_compFieldVars_2871_);
lean_closure_set(v___f_2911_, 2, v___x_2872_);
lean_closure_set(v___f_2911_, 3, v___x_2909_);
lean_closure_set(v___f_2911_, 4, v_params_2873_);
lean_closure_set(v___f_2911_, 5, v___x_2905_);
lean_closure_set(v___f_2911_, 6, v_a_2874_);
lean_closure_set(v___f_2911_, 7, v___x_2910_);
lean_inc(v___y_2883_);
lean_inc_ref(v___y_2882_);
lean_inc(v___y_2881_);
lean_inc_ref(v___y_2880_);
lean_inc_ref(v___y_2879_);
v___x_2912_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2908_, v___f_2911_, v___x_2875_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_, v___y_2883_);
v___y_2891_ = v___x_2912_;
goto v___jp_2890_;
}
else
{
lean_dec_ref(v___x_2905_);
lean_dec(v_v_2887_);
v___y_2891_ = v___x_2907_;
goto v___jp_2890_;
}
v___jp_2890_:
{
if (lean_obj_tag(v___y_2891_) == 0)
{
lean_object* v_a_2892_; size_t v___x_2893_; size_t v___x_2894_; lean_object* v___x_2895_; 
v_a_2892_ = lean_ctor_get(v___y_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___y_2891_);
v___x_2893_ = ((size_t)1ULL);
v___x_2894_ = lean_usize_add(v_i_2877_, v___x_2893_);
v___x_2895_ = lean_array_uset(v_bs_x27_2889_, v_i_2877_, v_a_2892_);
v_i_2877_ = v___x_2894_;
v_bs_2878_ = v___x_2895_;
goto _start;
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec_ref(v_bs_x27_2889_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v_a_2874_);
lean_dec_ref(v_params_2873_);
lean_dec_ref(v___x_2872_);
lean_dec_ref(v_compFieldVars_2871_);
lean_dec(v_lparams_2870_);
v_a_2897_ = lean_ctor_get(v___y_2891_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___y_2891_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___y_2891_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___y_2891_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object* v_lparams_2913_, lean_object* v_compFieldVars_2914_, lean_object* v___x_2915_, lean_object* v_params_2916_, lean_object* v_a_2917_, lean_object* v___x_2918_, lean_object* v_sz_2919_, lean_object* v_i_2920_, lean_object* v_bs_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
uint8_t v___x_14710__boxed_2928_; size_t v_sz_boxed_2929_; size_t v_i_boxed_2930_; lean_object* v_res_2931_; 
v___x_14710__boxed_2928_ = lean_unbox(v___x_2918_);
v_sz_boxed_2929_ = lean_unbox_usize(v_sz_2919_);
lean_dec(v_sz_2919_);
v_i_boxed_2930_ = lean_unbox_usize(v_i_2920_);
lean_dec(v_i_2920_);
v_res_2931_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2913_, v_compFieldVars_2914_, v___x_2915_, v_params_2916_, v_a_2917_, v___x_14710__boxed_2928_, v_sz_boxed_2929_, v_i_boxed_2930_, v_bs_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2932_, size_t v_i_2933_, lean_object* v_bs_2934_){
_start:
{
uint8_t v___x_2935_; 
v___x_2935_ = lean_usize_dec_lt(v_i_2933_, v_sz_2932_);
if (v___x_2935_ == 0)
{
return v_bs_2934_;
}
else
{
lean_object* v_v_2936_; lean_object* v___x_2937_; lean_object* v_bs_x27_2938_; lean_object* v___x_2939_; size_t v___x_2940_; size_t v___x_2941_; lean_object* v___x_2942_; 
v_v_2936_ = lean_array_uget(v_bs_2934_, v_i_2933_);
v___x_2937_ = lean_unsigned_to_nat(0u);
v_bs_x27_2938_ = lean_array_uset(v_bs_2934_, v_i_2933_, v___x_2937_);
v___x_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2939_, 0, v_v_2936_);
v___x_2940_ = ((size_t)1ULL);
v___x_2941_ = lean_usize_add(v_i_2933_, v___x_2940_);
v___x_2942_ = lean_array_uset(v_bs_x27_2938_, v_i_2933_, v___x_2939_);
v_i_2933_ = v___x_2941_;
v_bs_2934_ = v___x_2942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2944_, lean_object* v_i_2945_, lean_object* v_bs_2946_){
_start:
{
size_t v_sz_boxed_2947_; size_t v_i_boxed_2948_; lean_object* v_res_2949_; 
v_sz_boxed_2947_ = lean_unbox_usize(v_sz_2944_);
lean_dec(v_sz_2944_);
v_i_boxed_2948_ = lean_unbox_usize(v_i_2945_);
lean_dec(v_i_2945_);
v_res_2949_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2947_, v_i_boxed_2948_, v_bs_2946_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2952_, lean_object* v_lparams_2953_, lean_object* v_compFieldVars_2954_, lean_object* v_params_2955_, lean_object* v_val_2956_, lean_object* v___x_2957_, lean_object* v_indices_2958_, lean_object* v_xImpl_2959_, lean_object* v___x_2960_, lean_object* v_levelParams_2961_, lean_object* v_as_2962_, size_t v_sz_2963_, size_t v_i_2964_, lean_object* v_b_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_a_2973_; uint8_t v___x_2977_; 
v___x_2977_ = lean_usize_dec_lt(v_i_2964_, v_sz_2963_);
if (v___x_2977_ == 0)
{
lean_object* v___x_2978_; 
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_b_2965_);
return v___x_2978_;
}
else
{
lean_object* v_array_2979_; lean_object* v_start_2980_; lean_object* v_stop_2981_; uint8_t v___x_2982_; 
v_array_2979_ = lean_ctor_get(v_b_2965_, 0);
v_start_2980_ = lean_ctor_get(v_b_2965_, 1);
v_stop_2981_ = lean_ctor_get(v_b_2965_, 2);
v___x_2982_ = lean_nat_dec_lt(v_start_2980_, v_stop_2981_);
if (v___x_2982_ == 0)
{
lean_object* v___x_2983_; 
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v___x_2983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2983_, 0, v_b_2965_);
return v___x_2983_;
}
else
{
lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3166_; 
lean_inc(v_stop_2981_);
lean_inc(v_start_2980_);
lean_inc_ref(v_array_2979_);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_b_2965_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; lean_object* v_unused_3169_; 
v_unused_3167_ = lean_ctor_get(v_b_2965_, 2);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_b_2965_, 1);
lean_dec(v_unused_3168_);
v_unused_3169_ = lean_ctor_get(v_b_2965_, 0);
lean_dec(v_unused_3169_);
v___x_2985_ = v_b_2965_;
v_isShared_2986_ = v_isSharedCheck_3166_;
goto v_resetjp_2984_;
}
else
{
lean_dec(v_b_2965_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3166_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2987_; lean_object* v_env_2988_; lean_object* v___x_2989_; lean_object* v_a_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2987_ = lean_st_ref_get(v___y_2970_);
v_env_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc_ref(v_env_2988_);
lean_dec(v___x_2987_);
v___x_2989_ = lean_array_fget(v_array_2979_, v_start_2980_);
v_a_2990_ = lean_array_uget_borrowed(v_as_2962_, v_i_2964_);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_start_2980_, v___x_2991_);
lean_dec(v_start_2980_);
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 1, v___x_2992_);
v___x_2994_ = v___x_2985_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_array_2979_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_stop_2981_);
v___x_2994_ = v_reuseFailAlloc_3165_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
uint8_t v___x_2995_; 
lean_inc(v_a_2990_);
v___x_2995_ = l_Lean_isExtern(v_env_2988_, v_a_2990_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2996_; size_t v_sz_2997_; size_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
lean_inc(v_ctors_2952_);
v___x_2996_ = lean_array_mk(v_ctors_2952_);
v_sz_2997_ = lean_array_size(v___x_2996_);
v___x_2998_ = ((size_t)0ULL);
v___x_2999_ = lean_box(v___x_2995_);
v___x_3000_ = lean_box_usize(v_sz_2997_);
v___x_3001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2990_);
lean_inc_ref(v_params_2955_);
lean_inc(v___x_2989_);
lean_inc_ref(v_compFieldVars_2954_);
lean_inc(v_lparams_2953_);
v___x_3002_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_3002_, 0, v_lparams_2953_);
lean_closure_set(v___x_3002_, 1, v_compFieldVars_2954_);
lean_closure_set(v___x_3002_, 2, v___x_2989_);
lean_closure_set(v___x_3002_, 3, v_params_2955_);
lean_closure_set(v___x_3002_, 4, v_a_2990_);
lean_closure_set(v___x_3002_, 5, v___x_2999_);
lean_closure_set(v___x_3002_, 6, v___x_3000_);
lean_closure_set(v___x_3002_, 7, v___x_3001_);
lean_closure_set(v___x_3002_, 8, v___x_2996_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc_ref(v___y_2966_);
v___x_3003_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3002_, v___x_2982_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3005_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref(v___x_3003_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc(v___x_2989_);
v___x_3005_ = lean_infer_type(v___x_2989_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref(v___x_3005_);
v___x_3007_ = lean_mk_empty_array_with_capacity(v___x_2991_);
lean_inc_ref(v_val_2956_);
lean_inc_ref(v___x_3007_);
v___x_3008_ = lean_array_push(v___x_3007_, v_val_2956_);
lean_inc_ref(v___x_2957_);
v___x_3009_ = l_Array_append___redArg(v___x_2957_, v___x_3008_);
lean_dec_ref(v___x_3008_);
v___x_3010_ = 1;
v___x_3011_ = l_Lean_Meta_mkForallFVars(v___x_3009_, v_a_3006_, v___x_2995_, v___x_2982_, v___x_2982_, v___x_3010_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref(v___x_3011_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
v___x_3013_ = lean_infer_type(v___x_2989_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref(v___x_3013_);
lean_inc_ref(v_xImpl_2959_);
lean_inc_ref(v_indices_2958_);
v___x_3015_ = lean_array_push(v_indices_2958_, v_xImpl_2959_);
v___x_3016_ = l_Lean_Meta_mkLambdaFVars(v___x_3015_, v_a_3014_, v___x_2995_, v___x_2982_, v___x_2995_, v___x_2982_, v___x_3010_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec_ref(v___x_3015_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref(v___x_3016_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc_ref(v_xImpl_2959_);
v___x_3018_ = lean_infer_type(v_xImpl_2959_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref(v___x_3018_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc_ref(v_val_2956_);
v___x_3020_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3019_, v_val_2956_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_object* v_a_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; size_t v_sz_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref(v___x_3020_);
lean_inc(v___x_2960_);
v___x_3022_ = l_Lean_mkCasesOnName(v___x_2960_);
lean_inc_ref(v___x_3007_);
v___x_3023_ = lean_array_push(v___x_3007_, v_a_3017_);
lean_inc_ref(v_params_2955_);
v___x_3024_ = l_Array_append___redArg(v_params_2955_, v___x_3023_);
lean_dec_ref(v___x_3023_);
v___x_3025_ = l_Array_append___redArg(v___x_3024_, v_indices_2958_);
v___x_3026_ = lean_array_push(v___x_3007_, v_a_3021_);
v___x_3027_ = l_Array_append___redArg(v___x_3025_, v___x_3026_);
lean_dec_ref(v___x_3026_);
v___x_3028_ = l_Array_append___redArg(v___x_3027_, v_a_3004_);
lean_dec(v_a_3004_);
v_sz_3029_ = lean_array_size(v___x_3028_);
v___x_3030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3029_, v___x_2998_, v___x_3028_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
v___x_3031_ = l_Lean_Meta_mkAppOptM(v___x_3022_, v___x_3030_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; lean_object* v___x_3033_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref(v___x_3031_);
v___x_3033_ = l_Lean_Meta_mkLambdaFVars(v___x_3009_, v_a_3032_, v___x_2995_, v___x_2982_, v___x_2995_, v___x_2982_, v___x_3010_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
lean_dec_ref(v___x_3009_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref(v___x_3033_);
v___x_3035_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2990_);
v___x_3036_ = l_Lean_Name_append(v_a_2990_, v___x_3035_);
lean_inc(v_levelParams_2961_);
lean_inc(v___x_3036_);
v___x_3052_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3036_);
lean_ctor_set(v___x_3052_, 1, v_levelParams_2961_);
lean_ctor_set(v___x_3052_, 2, v_a_3012_);
v___x_3053_ = lean_box(0);
v___x_3054_ = 0;
v___x_3055_ = lean_box(0);
lean_inc(v___x_3036_);
v___x_3056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3036_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3057_, 0, v___x_3052_);
lean_ctor_set(v___x_3057_, 1, v_a_3034_);
lean_ctor_set(v___x_3057_, 2, v___x_3053_);
lean_ctor_set(v___x_3057_, 3, v___x_3056_);
lean_ctor_set_uint8(v___x_3057_, sizeof(void*)*4, v___x_3054_);
v___x_3058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3057_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
v___x_3059_ = l_Lean_addDecl(v___x_3058_, v___x_2995_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v___x_3060_; lean_object* v_env_3061_; lean_object* v___x_3062_; 
lean_dec_ref(v___x_3059_);
v___x_3060_ = lean_st_ref_get(v___y_2970_);
v_env_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc_ref(v_env_3061_);
lean_dec(v___x_3060_);
lean_inc(v_a_2990_);
v___x_3062_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3061_, v_a_2990_);
if (lean_obj_tag(v___x_3062_) == 1)
{
lean_object* v_val_3063_; uint8_t v___x_3064_; lean_object* v___x_3065_; 
v_val_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_val_3063_);
lean_dec_ref(v___x_3062_);
v___x_3064_ = lean_unbox(v_val_3063_);
lean_dec(v_val_3063_);
lean_inc(v___x_3036_);
v___x_3065_ = l_Lean_Meta_setInlineAttribute(v___x_3036_, v___x_3064_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_dec_ref(v___x_3065_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc_ref(v___y_2966_);
v___y_3038_ = v___y_2966_;
v___y_3039_ = v___y_2967_;
v___y_3040_ = v___y_2968_;
v___y_3041_ = v___y_2969_;
v___y_3042_ = v___y_2970_;
goto v___jp_3037_;
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec(v___x_3036_);
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
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
lean_dec(v___x_3062_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc_ref(v___y_2966_);
v___y_3038_ = v___y_2966_;
v___y_3039_ = v___y_2967_;
v___y_3040_ = v___y_2968_;
v___y_3041_ = v___y_2969_;
v___y_3042_ = v___y_2970_;
goto v___jp_3037_;
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec(v___x_3036_);
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3074_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3059_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3059_);
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
v___jp_3037_:
{
lean_object* v___x_3043_; 
lean_inc(v_a_2990_);
v___x_3043_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2990_, v___x_3036_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec_ref(v___y_3038_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_dec_ref(v___x_3043_);
v_a_2973_ = v___x_2994_;
goto v___jp_2972_;
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3044_ = lean_ctor_get(v___x_3043_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3043_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v_a_3012_);
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3082_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3033_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3033_);
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
lean_dec(v_a_3012_);
lean_dec_ref(v___x_3009_);
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3090_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3031_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3031_);
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
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec_ref(v___x_3009_);
lean_dec_ref(v___x_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3098_ = lean_ctor_get(v___x_3020_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3020_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3020_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3020_);
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
lean_dec(v_a_3017_);
lean_dec(v_a_3012_);
lean_dec_ref(v___x_3009_);
lean_dec_ref(v___x_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3106_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3018_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3018_);
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
lean_dec(v_a_3012_);
lean_dec_ref(v___x_3009_);
lean_dec_ref(v___x_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3114_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3016_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3016_);
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
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_a_3012_);
lean_dec_ref(v___x_3009_);
lean_dec_ref(v___x_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3122_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3013_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3013_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3137_; 
lean_dec_ref(v___x_3009_);
lean_dec_ref(v___x_3007_);
lean_dec(v_a_3004_);
lean_dec_ref(v___x_2994_);
lean_dec(v___x_2989_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3130_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3137_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3137_ == 0)
{
v___x_3132_ = v___x_3011_;
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3011_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3137_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3135_; 
if (v_isShared_3133_ == 0)
{
v___x_3135_ = v___x_3132_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3130_);
v___x_3135_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
return v___x_3135_;
}
}
}
}
else
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v_a_3004_);
lean_dec_ref(v___x_2994_);
lean_dec(v___x_2989_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3138_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3140_ = v___x_3005_;
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3005_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3145_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3143_; 
if (v_isShared_3141_ == 0)
{
v___x_3143_ = v___x_3140_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3138_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
else
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
lean_dec_ref(v___x_2994_);
lean_dec(v___x_2989_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3146_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v___x_3003_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3003_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_dec(v___x_2989_);
v___x_3154_ = lean_mk_empty_array_with_capacity(v___x_2991_);
lean_inc(v_a_2990_);
v___x_3155_ = lean_array_push(v___x_3154_, v_a_2990_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
v___x_3156_ = l_Lean_compileDecls(v___x_3155_, v___x_2982_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_dec_ref(v___x_3156_);
v_a_2973_ = v___x_2994_;
goto v___jp_2972_;
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref(v___x_2994_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v_levelParams_2961_);
lean_dec(v___x_2960_);
lean_dec_ref(v_xImpl_2959_);
lean_dec_ref(v_indices_2958_);
lean_dec_ref(v___x_2957_);
lean_dec_ref(v_val_2956_);
lean_dec_ref(v_params_2955_);
lean_dec_ref(v_compFieldVars_2954_);
lean_dec(v_lparams_2953_);
lean_dec(v_ctors_2952_);
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
}
}
}
v___jp_2972_:
{
size_t v___x_2974_; size_t v___x_2975_; 
v___x_2974_ = ((size_t)1ULL);
v___x_2975_ = lean_usize_add(v_i_2964_, v___x_2974_);
v_i_2964_ = v___x_2975_;
v_b_2965_ = v_a_2973_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3170_ = _args[0];
lean_object* v_lparams_3171_ = _args[1];
lean_object* v_compFieldVars_3172_ = _args[2];
lean_object* v_params_3173_ = _args[3];
lean_object* v_val_3174_ = _args[4];
lean_object* v___x_3175_ = _args[5];
lean_object* v_indices_3176_ = _args[6];
lean_object* v_xImpl_3177_ = _args[7];
lean_object* v___x_3178_ = _args[8];
lean_object* v_levelParams_3179_ = _args[9];
lean_object* v_as_3180_ = _args[10];
lean_object* v_sz_3181_ = _args[11];
lean_object* v_i_3182_ = _args[12];
lean_object* v_b_3183_ = _args[13];
lean_object* v___y_3184_ = _args[14];
lean_object* v___y_3185_ = _args[15];
lean_object* v___y_3186_ = _args[16];
lean_object* v___y_3187_ = _args[17];
lean_object* v___y_3188_ = _args[18];
lean_object* v___y_3189_ = _args[19];
_start:
{
size_t v_sz_boxed_3190_; size_t v_i_boxed_3191_; lean_object* v_res_3192_; 
v_sz_boxed_3190_ = lean_unbox_usize(v_sz_3181_);
lean_dec(v_sz_3181_);
v_i_boxed_3191_ = lean_unbox_usize(v_i_3182_);
lean_dec(v_i_3182_);
v_res_3192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3170_, v_lparams_3171_, v_compFieldVars_3172_, v_params_3173_, v_val_3174_, v___x_3175_, v_indices_3176_, v_xImpl_3177_, v___x_3178_, v_levelParams_3179_, v_as_3180_, v_sz_boxed_3190_, v_i_boxed_3191_, v_b_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec_ref(v_as_3180_);
return v_res_3192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3193_, lean_object* v_compFieldVars_3194_, lean_object* v_params_3195_, lean_object* v_ctors_3196_, lean_object* v_val_3197_, lean_object* v___x_3198_, lean_object* v_indices_3199_, lean_object* v_xImpl_3200_, lean_object* v___x_3201_, lean_object* v_levelParams_3202_, lean_object* v_as_3203_, size_t v_sz_3204_, size_t v_i_3205_, lean_object* v_b_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_a_3214_; uint8_t v___x_3218_; 
v___x_3218_ = lean_usize_dec_lt(v_i_3205_, v_sz_3204_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; 
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v_b_3206_);
return v___x_3219_;
}
else
{
lean_object* v_array_3220_; lean_object* v_start_3221_; lean_object* v_stop_3222_; uint8_t v___x_3223_; 
v_array_3220_ = lean_ctor_get(v_b_3206_, 0);
v_start_3221_ = lean_ctor_get(v_b_3206_, 1);
v_stop_3222_ = lean_ctor_get(v_b_3206_, 2);
v___x_3223_ = lean_nat_dec_lt(v_start_3221_, v_stop_3222_);
if (v___x_3223_ == 0)
{
lean_object* v___x_3224_; 
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v_b_3206_);
return v___x_3224_;
}
else
{
lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3407_; 
lean_inc(v_stop_3222_);
lean_inc(v_start_3221_);
lean_inc_ref(v_array_3220_);
v_isSharedCheck_3407_ = !lean_is_exclusive(v_b_3206_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; lean_object* v_unused_3409_; lean_object* v_unused_3410_; 
v_unused_3408_ = lean_ctor_get(v_b_3206_, 2);
lean_dec(v_unused_3408_);
v_unused_3409_ = lean_ctor_get(v_b_3206_, 1);
lean_dec(v_unused_3409_);
v_unused_3410_ = lean_ctor_get(v_b_3206_, 0);
lean_dec(v_unused_3410_);
v___x_3226_ = v_b_3206_;
v_isShared_3227_ = v_isSharedCheck_3407_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v_b_3206_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3407_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v_env_3229_; lean_object* v___x_3230_; lean_object* v_a_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3228_ = lean_st_ref_get(v___y_3211_);
v_env_3229_ = lean_ctor_get(v___x_3228_, 0);
lean_inc_ref(v_env_3229_);
lean_dec(v___x_3228_);
v___x_3230_ = lean_array_fget(v_array_3220_, v_start_3221_);
v_a_3231_ = lean_array_uget_borrowed(v_as_3203_, v_i_3205_);
v___x_3232_ = lean_unsigned_to_nat(1u);
v___x_3233_ = lean_nat_add(v_start_3221_, v___x_3232_);
lean_dec(v_start_3221_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 1, v___x_3233_);
v___x_3235_ = v___x_3226_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_array_3220_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_stop_3222_);
v___x_3235_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
uint8_t v___x_3236_; 
lean_inc(v_a_3231_);
v___x_3236_ = l_Lean_isExtern(v_env_3229_, v_a_3231_);
if (v___x_3236_ == 0)
{
lean_object* v___x_3237_; size_t v_sz_3238_; size_t v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
lean_inc(v_ctors_3196_);
v___x_3237_ = lean_array_mk(v_ctors_3196_);
v_sz_3238_ = lean_array_size(v___x_3237_);
v___x_3239_ = ((size_t)0ULL);
v___x_3240_ = lean_box(v___x_3236_);
v___x_3241_ = lean_box_usize(v_sz_3238_);
v___x_3242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3231_);
lean_inc_ref(v_params_3195_);
lean_inc(v___x_3230_);
lean_inc_ref(v_compFieldVars_3194_);
lean_inc(v_lparams_3193_);
v___x_3243_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_3243_, 0, v_lparams_3193_);
lean_closure_set(v___x_3243_, 1, v_compFieldVars_3194_);
lean_closure_set(v___x_3243_, 2, v___x_3230_);
lean_closure_set(v___x_3243_, 3, v_params_3195_);
lean_closure_set(v___x_3243_, 4, v_a_3231_);
lean_closure_set(v___x_3243_, 5, v___x_3240_);
lean_closure_set(v___x_3243_, 6, v___x_3241_);
lean_closure_set(v___x_3243_, 7, v___x_3242_);
lean_closure_set(v___x_3243_, 8, v___x_3237_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc_ref(v___y_3207_);
v___x_3244_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3243_, v___x_3223_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref(v___x_3244_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc(v___x_3230_);
v___x_3246_ = lean_infer_type(v___x_3230_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; lean_object* v___x_3252_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref(v___x_3246_);
v___x_3248_ = lean_mk_empty_array_with_capacity(v___x_3232_);
lean_inc_ref(v_val_3197_);
lean_inc_ref(v___x_3248_);
v___x_3249_ = lean_array_push(v___x_3248_, v_val_3197_);
lean_inc_ref(v___x_3198_);
v___x_3250_ = l_Array_append___redArg(v___x_3198_, v___x_3249_);
lean_dec_ref(v___x_3249_);
v___x_3251_ = 1;
v___x_3252_ = l_Lean_Meta_mkForallFVars(v___x_3250_, v_a_3247_, v___x_3236_, v___x_3223_, v___x_3223_, v___x_3251_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref(v___x_3252_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
v___x_3254_ = lean_infer_type(v___x_3230_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
lean_inc(v_a_3255_);
lean_dec_ref(v___x_3254_);
lean_inc_ref(v_xImpl_3200_);
lean_inc_ref(v_indices_3199_);
v___x_3256_ = lean_array_push(v_indices_3199_, v_xImpl_3200_);
v___x_3257_ = l_Lean_Meta_mkLambdaFVars(v___x_3256_, v_a_3255_, v___x_3236_, v___x_3223_, v___x_3236_, v___x_3223_, v___x_3251_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec_ref(v___x_3256_);
if (lean_obj_tag(v___x_3257_) == 0)
{
lean_object* v_a_3258_; lean_object* v___x_3259_; 
v_a_3258_ = lean_ctor_get(v___x_3257_, 0);
lean_inc(v_a_3258_);
lean_dec_ref(v___x_3257_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc_ref(v_xImpl_3200_);
v___x_3259_ = lean_infer_type(v_xImpl_3200_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; lean_object* v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref(v___x_3259_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc_ref(v_val_3197_);
v___x_3261_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3260_, v_val_3197_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v_a_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; size_t v_sz_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
lean_inc(v_a_3262_);
lean_dec_ref(v___x_3261_);
lean_inc(v___x_3201_);
v___x_3263_ = l_Lean_mkCasesOnName(v___x_3201_);
lean_inc_ref(v___x_3248_);
v___x_3264_ = lean_array_push(v___x_3248_, v_a_3258_);
lean_inc_ref(v_params_3195_);
v___x_3265_ = l_Array_append___redArg(v_params_3195_, v___x_3264_);
lean_dec_ref(v___x_3264_);
v___x_3266_ = l_Array_append___redArg(v___x_3265_, v_indices_3199_);
v___x_3267_ = lean_array_push(v___x_3248_, v_a_3262_);
v___x_3268_ = l_Array_append___redArg(v___x_3266_, v___x_3267_);
lean_dec_ref(v___x_3267_);
v___x_3269_ = l_Array_append___redArg(v___x_3268_, v_a_3245_);
lean_dec(v_a_3245_);
v_sz_3270_ = lean_array_size(v___x_3269_);
v___x_3271_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3270_, v___x_3239_, v___x_3269_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
v___x_3272_ = l_Lean_Meta_mkAppOptM(v___x_3263_, v___x_3271_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3274_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref(v___x_3272_);
v___x_3274_ = l_Lean_Meta_mkLambdaFVars(v___x_3250_, v_a_3273_, v___x_3236_, v___x_3223_, v___x_3236_, v___x_3223_, v___x_3251_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
lean_dec_ref(v___x_3250_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___y_3279_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3231_);
v___x_3277_ = l_Lean_Name_append(v_a_3231_, v___x_3276_);
lean_inc(v_levelParams_3202_);
lean_inc(v___x_3277_);
v___x_3293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3277_);
lean_ctor_set(v___x_3293_, 1, v_levelParams_3202_);
lean_ctor_set(v___x_3293_, 2, v_a_3253_);
v___x_3294_ = lean_box(0);
v___x_3295_ = 0;
v___x_3296_ = lean_box(0);
lean_inc(v___x_3277_);
v___x_3297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3277_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3298_, 0, v___x_3293_);
lean_ctor_set(v___x_3298_, 1, v_a_3275_);
lean_ctor_set(v___x_3298_, 2, v___x_3294_);
lean_ctor_set(v___x_3298_, 3, v___x_3297_);
lean_ctor_set_uint8(v___x_3298_, sizeof(void*)*4, v___x_3295_);
v___x_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3298_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
v___x_3300_ = l_Lean_addDecl(v___x_3299_, v___x_3236_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v___x_3301_; lean_object* v_env_3302_; lean_object* v___x_3303_; 
lean_dec_ref(v___x_3300_);
v___x_3301_ = lean_st_ref_get(v___y_3211_);
v_env_3302_ = lean_ctor_get(v___x_3301_, 0);
lean_inc_ref(v_env_3302_);
lean_dec(v___x_3301_);
lean_inc(v_a_3231_);
v___x_3303_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3302_, v_a_3231_);
if (lean_obj_tag(v___x_3303_) == 1)
{
lean_object* v_val_3304_; uint8_t v___x_3305_; lean_object* v___x_3306_; 
v_val_3304_ = lean_ctor_get(v___x_3303_, 0);
lean_inc(v_val_3304_);
lean_dec_ref(v___x_3303_);
v___x_3305_ = lean_unbox(v_val_3304_);
lean_dec(v_val_3304_);
lean_inc(v___x_3277_);
v___x_3306_ = l_Lean_Meta_setInlineAttribute(v___x_3277_, v___x_3305_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3306_) == 0)
{
lean_dec_ref(v___x_3306_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc_ref(v___y_3207_);
v___y_3279_ = v___y_3207_;
v___y_3280_ = v___y_3208_;
v___y_3281_ = v___y_3209_;
v___y_3282_ = v___y_3210_;
v___y_3283_ = v___y_3211_;
goto v___jp_3278_;
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v___x_3277_);
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3307_ = lean_ctor_get(v___x_3306_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3306_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3306_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3306_);
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
lean_dec(v___x_3303_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
lean_inc(v___y_3209_);
lean_inc_ref(v___y_3208_);
lean_inc_ref(v___y_3207_);
v___y_3279_ = v___y_3207_;
v___y_3280_ = v___y_3208_;
v___y_3281_ = v___y_3209_;
v___y_3282_ = v___y_3210_;
v___y_3283_ = v___y_3211_;
goto v___jp_3278_;
}
}
else
{
lean_object* v_a_3315_; lean_object* v___x_3317_; uint8_t v_isShared_3318_; uint8_t v_isSharedCheck_3322_; 
lean_dec(v___x_3277_);
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3315_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3317_ = v___x_3300_;
v_isShared_3318_ = v_isSharedCheck_3322_;
goto v_resetjp_3316_;
}
else
{
lean_inc(v_a_3315_);
lean_dec(v___x_3300_);
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
v___jp_3278_:
{
lean_object* v___x_3284_; 
lean_inc(v_a_3231_);
v___x_3284_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3231_, v___x_3277_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec(v___y_3281_);
lean_dec_ref(v___y_3280_);
lean_dec_ref(v___y_3279_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_dec_ref(v___x_3284_);
v_a_3214_ = v___x_3235_;
goto v___jp_3213_;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_a_3253_);
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3323_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3274_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3274_);
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
lean_dec(v_a_3253_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3331_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3272_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3272_);
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
lean_dec(v_a_3258_);
lean_dec(v_a_3253_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3248_);
lean_dec(v_a_3245_);
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3339_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3261_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3261_);
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
lean_dec(v_a_3258_);
lean_dec(v_a_3253_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3248_);
lean_dec(v_a_3245_);
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3347_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3354_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3354_ == 0)
{
v___x_3349_ = v___x_3259_;
v_isShared_3350_ = v_isSharedCheck_3354_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_a_3347_);
lean_dec(v___x_3259_);
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
lean_dec(v_a_3253_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3248_);
lean_dec(v_a_3245_);
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3355_ = lean_ctor_get(v___x_3257_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3257_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3257_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3257_);
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
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3370_; 
lean_dec(v_a_3253_);
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3248_);
lean_dec(v_a_3245_);
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3363_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3370_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3370_ == 0)
{
v___x_3365_ = v___x_3254_;
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3254_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3370_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3368_; 
if (v_isShared_3366_ == 0)
{
v___x_3368_ = v___x_3365_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3363_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
else
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v___x_3250_);
lean_dec_ref(v___x_3248_);
lean_dec(v_a_3245_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3230_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3371_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3373_ = v___x_3252_;
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3252_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3378_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3376_; 
if (v_isShared_3374_ == 0)
{
v___x_3376_ = v___x_3373_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_a_3371_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
return v___x_3376_;
}
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
lean_dec(v_a_3245_);
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3230_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3379_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3246_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3246_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v___x_3235_);
lean_dec(v___x_3230_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3387_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3244_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3244_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; 
lean_dec(v___x_3230_);
v___x_3395_ = lean_mk_empty_array_with_capacity(v___x_3232_);
lean_inc(v_a_3231_);
v___x_3396_ = lean_array_push(v___x_3395_, v_a_3231_);
lean_inc(v___y_3211_);
lean_inc_ref(v___y_3210_);
v___x_3397_ = l_Lean_compileDecls(v___x_3396_, v___x_3223_, v___y_3210_, v___y_3211_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_dec_ref(v___x_3397_);
v_a_3214_ = v___x_3235_;
goto v___jp_3213_;
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
lean_dec_ref(v___x_3235_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec_ref(v___y_3207_);
lean_dec(v_levelParams_3202_);
lean_dec(v___x_3201_);
lean_dec_ref(v_xImpl_3200_);
lean_dec_ref(v_indices_3199_);
lean_dec_ref(v___x_3198_);
lean_dec_ref(v_val_3197_);
lean_dec(v_ctors_3196_);
lean_dec_ref(v_params_3195_);
lean_dec_ref(v_compFieldVars_3194_);
lean_dec(v_lparams_3193_);
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
}
}
}
}
v___jp_3213_:
{
size_t v___x_3215_; size_t v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = ((size_t)1ULL);
v___x_3216_ = lean_usize_add(v_i_3205_, v___x_3215_);
v___x_3217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3196_, v_lparams_3193_, v_compFieldVars_3194_, v_params_3195_, v_val_3197_, v___x_3198_, v_indices_3199_, v_xImpl_3200_, v___x_3201_, v_levelParams_3202_, v_as_3203_, v_sz_3204_, v___x_3216_, v_a_3214_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3411_ = _args[0];
lean_object* v_compFieldVars_3412_ = _args[1];
lean_object* v_params_3413_ = _args[2];
lean_object* v_ctors_3414_ = _args[3];
lean_object* v_val_3415_ = _args[4];
lean_object* v___x_3416_ = _args[5];
lean_object* v_indices_3417_ = _args[6];
lean_object* v_xImpl_3418_ = _args[7];
lean_object* v___x_3419_ = _args[8];
lean_object* v_levelParams_3420_ = _args[9];
lean_object* v_as_3421_ = _args[10];
lean_object* v_sz_3422_ = _args[11];
lean_object* v_i_3423_ = _args[12];
lean_object* v_b_3424_ = _args[13];
lean_object* v___y_3425_ = _args[14];
lean_object* v___y_3426_ = _args[15];
lean_object* v___y_3427_ = _args[16];
lean_object* v___y_3428_ = _args[17];
lean_object* v___y_3429_ = _args[18];
lean_object* v___y_3430_ = _args[19];
_start:
{
size_t v_sz_boxed_3431_; size_t v_i_boxed_3432_; lean_object* v_res_3433_; 
v_sz_boxed_3431_ = lean_unbox_usize(v_sz_3422_);
lean_dec(v_sz_3422_);
v_i_boxed_3432_ = lean_unbox_usize(v_i_3423_);
lean_dec(v_i_3423_);
v_res_3433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3411_, v_compFieldVars_3412_, v_params_3413_, v_ctors_3414_, v_val_3415_, v___x_3416_, v_indices_3417_, v_xImpl_3418_, v___x_3419_, v_levelParams_3420_, v_as_3421_, v_sz_boxed_3431_, v_i_boxed_3432_, v_b_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec_ref(v_as_3421_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3434_, lean_object* v_compFields_3435_, lean_object* v_lparams_3436_, lean_object* v_params_3437_, lean_object* v_ctors_3438_, lean_object* v_val_3439_, lean_object* v___x_3440_, lean_object* v_indices_3441_, lean_object* v___x_3442_, lean_object* v_levelParams_3443_, lean_object* v_xImpl_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; size_t v_sz_3454_; size_t v___x_3455_; lean_object* v___x_3456_; 
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = lean_array_get_size(v_compFieldVars_3434_);
lean_inc_ref(v_compFieldVars_3434_);
v___x_3453_ = l_Array_toSubarray___redArg(v_compFieldVars_3434_, v___x_3451_, v___x_3452_);
v_sz_3454_ = lean_array_size(v_compFields_3435_);
v___x_3455_ = ((size_t)0ULL);
v___x_3456_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3436_, v_compFieldVars_3434_, v_params_3437_, v_ctors_3438_, v_val_3439_, v___x_3440_, v_indices_3441_, v_xImpl_3444_, v___x_3442_, v_levelParams_3443_, v_compFields_3435_, v_sz_3454_, v___x_3455_, v___x_3453_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3464_; 
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3464_ == 0)
{
lean_object* v_unused_3465_; 
v_unused_3465_ = lean_ctor_get(v___x_3456_, 0);
lean_dec(v_unused_3465_);
v___x_3458_ = v___x_3456_;
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v___x_3456_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3464_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3460_ = lean_box(0);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3460_);
v___x_3462_ = v___x_3458_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
v_a_3466_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3456_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3456_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3474_ = _args[0];
lean_object* v_compFields_3475_ = _args[1];
lean_object* v_lparams_3476_ = _args[2];
lean_object* v_params_3477_ = _args[3];
lean_object* v_ctors_3478_ = _args[4];
lean_object* v_val_3479_ = _args[5];
lean_object* v___x_3480_ = _args[6];
lean_object* v_indices_3481_ = _args[7];
lean_object* v___x_3482_ = _args[8];
lean_object* v_levelParams_3483_ = _args[9];
lean_object* v_xImpl_3484_ = _args[10];
lean_object* v___y_3485_ = _args[11];
lean_object* v___y_3486_ = _args[12];
lean_object* v___y_3487_ = _args[13];
lean_object* v___y_3488_ = _args[14];
lean_object* v___y_3489_ = _args[15];
lean_object* v___y_3490_ = _args[16];
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3474_, v_compFields_3475_, v_lparams_3476_, v_params_3477_, v_ctors_3478_, v_val_3479_, v___x_3480_, v_indices_3481_, v___x_3482_, v_levelParams_3483_, v_xImpl_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
lean_dec_ref(v_compFields_3475_);
return v_res_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_){
_start:
{
lean_object* v_toInductiveVal_3501_; lean_object* v_toConstantVal_3502_; lean_object* v_lparams_3503_; lean_object* v_params_3504_; lean_object* v_compFields_3505_; lean_object* v_compFieldVars_3506_; lean_object* v_indices_3507_; lean_object* v_val_3508_; lean_object* v_ctors_3509_; lean_object* v_name_3510_; lean_object* v_levelParams_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___f_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v_toInductiveVal_3501_ = lean_ctor_get(v_a_3495_, 0);
v_toConstantVal_3502_ = lean_ctor_get(v_toInductiveVal_3501_, 0);
v_lparams_3503_ = lean_ctor_get(v_a_3495_, 1);
v_params_3504_ = lean_ctor_get(v_a_3495_, 2);
v_compFields_3505_ = lean_ctor_get(v_a_3495_, 3);
v_compFieldVars_3506_ = lean_ctor_get(v_a_3495_, 4);
v_indices_3507_ = lean_ctor_get(v_a_3495_, 5);
v_val_3508_ = lean_ctor_get(v_a_3495_, 6);
v_ctors_3509_ = lean_ctor_get(v_toInductiveVal_3501_, 4);
v_name_3510_ = lean_ctor_get(v_toConstantVal_3502_, 0);
v_levelParams_3511_ = lean_ctor_get(v_toConstantVal_3502_, 1);
v___x_3512_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3513_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_3510_);
v___x_3514_ = l_Lean_Name_append(v_name_3510_, v___x_3513_);
lean_inc(v_lparams_3503_);
lean_inc(v___x_3514_);
v___x_3515_ = l_Lean_mkConst(v___x_3514_, v_lparams_3503_);
lean_inc_ref(v_params_3504_);
v___x_3516_ = l_Array_append___redArg(v_params_3504_, v_indices_3507_);
lean_inc(v_levelParams_3511_);
lean_inc_ref(v_indices_3507_);
lean_inc_ref(v___x_3516_);
lean_inc_ref(v_val_3508_);
lean_inc(v_ctors_3509_);
lean_inc_ref(v_params_3504_);
lean_inc(v_lparams_3503_);
lean_inc_ref(v_compFields_3505_);
lean_inc_ref(v_compFieldVars_3506_);
v___f_3517_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3517_, 0, v_compFieldVars_3506_);
lean_closure_set(v___f_3517_, 1, v_compFields_3505_);
lean_closure_set(v___f_3517_, 2, v_lparams_3503_);
lean_closure_set(v___f_3517_, 3, v_params_3504_);
lean_closure_set(v___f_3517_, 4, v_ctors_3509_);
lean_closure_set(v___f_3517_, 5, v_val_3508_);
lean_closure_set(v___f_3517_, 6, v___x_3516_);
lean_closure_set(v___f_3517_, 7, v_indices_3507_);
lean_closure_set(v___f_3517_, 8, v___x_3514_);
lean_closure_set(v___f_3517_, 9, v_levelParams_3511_);
v___x_3518_ = l_Lean_mkAppN(v___x_3515_, v___x_3516_);
lean_dec_ref(v___x_3516_);
v___x_3519_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3512_, v___x_3518_, v___f_3517_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3527_, lean_object* v_b_3528_, lean_object* v_c_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v___x_3535_; 
v___x_3535_ = lean_apply_7(v_k_3527_, v_b_3528_, v_c_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_, lean_box(0));
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3536_, lean_object* v_b_3537_, lean_object* v_c_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3536_, v_b_3537_, v_c_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
return v_res_3544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3545_, lean_object* v_k_3546_, uint8_t v_cleanupAnnotations_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
lean_object* v___f_3553_; uint8_t v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___f_3553_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3553_, 0, v_k_3546_);
v___x_3554_ = 0;
v___x_3555_ = lean_box(0);
v___x_3556_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3554_, v___x_3555_, v_type_3545_, v___f_3553_, v_cleanupAnnotations_3547_, v___x_3554_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3556_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3556_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
v_a_3565_ = lean_ctor_get(v___x_3556_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3556_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3556_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3556_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3573_, lean_object* v_k_3574_, lean_object* v_cleanupAnnotations_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3581_; lean_object* v_res_3582_; 
v_cleanupAnnotations_boxed_3581_ = lean_unbox(v_cleanupAnnotations_3575_);
v_res_3582_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3573_, v_k_3574_, v_cleanupAnnotations_boxed_3581_, v___y_3576_, v___y_3577_, v___y_3578_, v___y_3579_);
return v_res_3582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3583_, lean_object* v_type_3584_, lean_object* v_k_3585_, uint8_t v_cleanupAnnotations_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3584_, v_k_3585_, v_cleanupAnnotations_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3593_, lean_object* v_type_3594_, lean_object* v_k_3595_, lean_object* v_cleanupAnnotations_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3602_; lean_object* v_res_3603_; 
v_cleanupAnnotations_boxed_3602_ = lean_unbox(v_cleanupAnnotations_3596_);
v_res_3603_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3593_, v_type_3594_, v_k_3595_, v_cleanupAnnotations_boxed_3602_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v_res_3603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3604_, lean_object* v___x_3605_, lean_object* v___x_3606_, lean_object* v_compFields_3607_, lean_object* v___x_3608_, lean_object* v_val_3609_, lean_object* v_compFieldVars_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_){
_start:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3616_, 0, v_a_3604_);
lean_ctor_set(v___x_3616_, 1, v___x_3605_);
lean_ctor_set(v___x_3616_, 2, v___x_3606_);
lean_ctor_set(v___x_3616_, 3, v_compFields_3607_);
lean_ctor_set(v___x_3616_, 4, v_compFieldVars_3610_);
lean_ctor_set(v___x_3616_, 5, v___x_3608_);
lean_ctor_set(v___x_3616_, 6, v_val_3609_);
lean_inc(v___y_3614_);
lean_inc_ref(v___y_3613_);
lean_inc(v___y_3612_);
lean_inc_ref(v___y_3611_);
v___x_3617_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3616_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v___x_3618_; 
lean_dec_ref(v___x_3617_);
lean_inc(v___y_3614_);
lean_inc_ref(v___y_3613_);
lean_inc(v___y_3612_);
lean_inc_ref(v___y_3611_);
lean_inc_ref(v___x_3616_);
v___x_3618_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3616_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v___x_3619_; 
lean_dec_ref(v___x_3618_);
lean_inc(v___y_3614_);
lean_inc_ref(v___y_3613_);
lean_inc(v___y_3612_);
lean_inc_ref(v___y_3611_);
lean_inc_ref(v___x_3616_);
v___x_3619_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3616_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v___x_3620_; 
lean_dec_ref(v___x_3619_);
lean_inc(v___y_3614_);
lean_inc_ref(v___y_3613_);
lean_inc(v___y_3612_);
lean_inc_ref(v___y_3611_);
lean_inc_ref(v___x_3616_);
v___x_3620_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3616_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v___x_3621_; 
lean_dec_ref(v___x_3620_);
v___x_3621_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3616_, v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
return v___x_3621_;
}
else
{
lean_dec_ref(v___x_3616_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v___x_3620_;
}
}
else
{
lean_dec_ref(v___x_3616_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v___x_3619_;
}
}
else
{
lean_dec_ref(v___x_3616_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v___x_3618_;
}
}
else
{
lean_dec_ref(v___x_3616_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v___x_3617_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3622_, lean_object* v___x_3623_, lean_object* v___x_3624_, lean_object* v_compFields_3625_, lean_object* v___x_3626_, lean_object* v_val_3627_, lean_object* v_compFieldVars_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3622_, v___x_3623_, v___x_3624_, v_compFields_3625_, v___x_3626_, v_val_3627_, v_compFieldVars_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3635_, lean_object* v___x_3636_, lean_object* v_val_3637_, lean_object* v_v_3638_, lean_object* v_x_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3645_ = l_Array_append___redArg(v___x_3635_, v___x_3636_);
v___x_3646_ = lean_unsigned_to_nat(1u);
v___x_3647_ = lean_mk_empty_array_with_capacity(v___x_3646_);
v___x_3648_ = lean_array_push(v___x_3647_, v_val_3637_);
v___x_3649_ = l_Array_append___redArg(v___x_3645_, v___x_3648_);
lean_dec_ref(v___x_3648_);
lean_inc(v___y_3643_);
lean_inc_ref(v___y_3642_);
lean_inc(v___y_3641_);
lean_inc_ref(v___y_3640_);
v___x_3650_ = l_Lean_Meta_mkAppM(v_v_3638_, v___x_3649_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; lean_object* v___x_3652_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref(v___x_3650_);
v___x_3652_ = lean_infer_type(v_a_3651_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_);
return v___x_3652_;
}
else
{
lean_dec(v___y_3643_);
lean_dec_ref(v___y_3642_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
return v___x_3650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3653_, lean_object* v___x_3654_, lean_object* v_val_3655_, lean_object* v_v_3656_, lean_object* v_x_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3653_, v___x_3654_, v_val_3655_, v_v_3656_, v_x_3657_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
lean_dec_ref(v_x_3657_);
lean_dec_ref(v___x_3654_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3664_, lean_object* v___x_3665_, lean_object* v_val_3666_, size_t v_sz_3667_, size_t v_i_3668_, lean_object* v_bs_3669_){
_start:
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_usize_dec_lt(v_i_3668_, v_sz_3667_);
if (v___x_3670_ == 0)
{
lean_dec_ref(v_val_3666_);
lean_dec_ref(v___x_3665_);
lean_dec_ref(v___x_3664_);
return v_bs_3669_;
}
else
{
lean_object* v_v_3671_; lean_object* v___f_3672_; lean_object* v___x_3673_; lean_object* v_bs_x27_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; size_t v___x_3678_; size_t v___x_3679_; lean_object* v___x_3680_; 
v_v_3671_ = lean_array_uget(v_bs_3669_, v_i_3668_);
lean_inc(v_v_3671_);
lean_inc_ref(v_val_3666_);
lean_inc_ref(v___x_3665_);
lean_inc_ref(v___x_3664_);
v___f_3672_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3672_, 0, v___x_3664_);
lean_closure_set(v___f_3672_, 1, v___x_3665_);
lean_closure_set(v___f_3672_, 2, v_val_3666_);
lean_closure_set(v___f_3672_, 3, v_v_3671_);
v___x_3673_ = lean_unsigned_to_nat(0u);
v_bs_x27_3674_ = lean_array_uset(v_bs_3669_, v_i_3668_, v___x_3673_);
v___x_3675_ = lean_box(0);
v___x_3676_ = l_Lean_Name_updatePrefix(v_v_3671_, v___x_3675_);
v___x_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
lean_ctor_set(v___x_3677_, 1, v___f_3672_);
v___x_3678_ = ((size_t)1ULL);
v___x_3679_ = lean_usize_add(v_i_3668_, v___x_3678_);
v___x_3680_ = lean_array_uset(v_bs_x27_3674_, v_i_3668_, v___x_3677_);
v_i_3668_ = v___x_3679_;
v_bs_3669_ = v___x_3680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3682_, lean_object* v___x_3683_, lean_object* v_val_3684_, lean_object* v_sz_3685_, lean_object* v_i_3686_, lean_object* v_bs_3687_){
_start:
{
size_t v_sz_boxed_3688_; size_t v_i_boxed_3689_; lean_object* v_res_3690_; 
v_sz_boxed_3688_ = lean_unbox_usize(v_sz_3685_);
lean_dec(v_sz_3685_);
v_i_boxed_3689_ = lean_unbox_usize(v_i_3686_);
lean_dec(v_i_3686_);
v_res_3690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3682_, v___x_3683_, v_val_3684_, v_sz_boxed_3688_, v_i_boxed_3689_, v_bs_3687_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0(lean_object* v___x_3691_, lean_object* v_a_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3134__overap_3699_; lean_object* v___x_3700_; 
v___x_3698_ = l_Lean_instInhabitedExpr;
v___x_3134__overap_3699_ = l_instInhabitedOfMonad___redArg(v___x_3691_, v___x_3698_);
v___x_3700_ = lean_apply_5(v___x_3134__overap_3699_, v___y_3693_, v___y_3694_, v___y_3695_, v___y_3696_, lean_box(0));
return v___x_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v___x_3701_, lean_object* v_a_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0(v___x_3701_, v_a_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec_ref(v_a_3702_);
return v_res_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_acc_3709_, lean_object* v_declInfos_3710_, lean_object* v_k_3711_, lean_object* v_kind_3712_, lean_object* v_inst_3713_, lean_object* v_b_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
uint8_t v_kind_boxed_3720_; lean_object* v_res_3721_; 
v_kind_boxed_3720_ = lean_unbox(v_kind_3712_);
v_res_3721_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0(v_acc_3709_, v_declInfos_3710_, v_k_3711_, v_kind_boxed_3720_, v_inst_3713_, v_b_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_acc_3722_, lean_object* v_declInfos_3723_, lean_object* v_k_3724_, uint8_t v_kind_3725_, lean_object* v_inst_3726_, lean_object* v_name_3727_, uint8_t v_bi_3728_, lean_object* v_type_3729_, uint8_t v_kind_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_){
_start:
{
lean_object* v___x_3736_; lean_object* v___f_3737_; lean_object* v___x_3738_; 
v___x_3736_ = lean_box(v_kind_3725_);
v___f_3737_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3737_, 0, v_acc_3722_);
lean_closure_set(v___f_3737_, 1, v_declInfos_3723_);
lean_closure_set(v___f_3737_, 2, v_k_3724_);
lean_closure_set(v___f_3737_, 3, v___x_3736_);
lean_closure_set(v___f_3737_, 4, v_inst_3726_);
v___x_3738_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3727_, v_bi_3728_, v_type_3729_, v___f_3737_, v_kind_3730_, v___y_3731_, v___y_3732_, v___y_3733_, v___y_3734_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
v_a_3747_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3738_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3738_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(lean_object* v_declInfos_3755_, lean_object* v_k_3756_, uint8_t v_kind_3757_, lean_object* v_inst_3758_, lean_object* v_acc_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v_toApplicative_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3852_; 
v___x_3765_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_3766_ = l_ReaderT_instMonad___redArg(v___x_3765_);
v_toApplicative_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3852_ == 0)
{
lean_object* v_unused_3853_; 
v_unused_3853_ = lean_ctor_get(v___x_3766_, 1);
lean_dec(v_unused_3853_);
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3852_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_toApplicative_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3852_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_toFunctor_3771_; lean_object* v_toSeq_3772_; lean_object* v_toSeqLeft_3773_; lean_object* v_toSeqRight_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3850_; 
v_toFunctor_3771_ = lean_ctor_get(v_toApplicative_3767_, 0);
v_toSeq_3772_ = lean_ctor_get(v_toApplicative_3767_, 2);
v_toSeqLeft_3773_ = lean_ctor_get(v_toApplicative_3767_, 3);
v_toSeqRight_3774_ = lean_ctor_get(v_toApplicative_3767_, 4);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_toApplicative_3767_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v_toApplicative_3767_, 1);
lean_dec(v_unused_3851_);
v___x_3776_ = v_toApplicative_3767_;
v_isShared_3777_ = v_isSharedCheck_3850_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_toSeqRight_3774_);
lean_inc(v_toSeqLeft_3773_);
lean_inc(v_toSeq_3772_);
lean_inc(v_toFunctor_3771_);
lean_dec(v_toApplicative_3767_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3850_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___f_3778_; lean_object* v___f_3779_; lean_object* v___f_3780_; lean_object* v___f_3781_; lean_object* v___x_3782_; lean_object* v___f_3783_; lean_object* v___f_3784_; lean_object* v___f_3785_; lean_object* v___x_3787_; 
v___f_3778_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_3779_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_3771_);
v___f_3780_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3780_, 0, v_toFunctor_3771_);
v___f_3781_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3781_, 0, v_toFunctor_3771_);
v___x_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___f_3780_);
lean_ctor_set(v___x_3782_, 1, v___f_3781_);
v___f_3783_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3783_, 0, v_toSeqRight_3774_);
v___f_3784_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3784_, 0, v_toSeqLeft_3773_);
v___f_3785_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3785_, 0, v_toSeq_3772_);
if (v_isShared_3777_ == 0)
{
lean_ctor_set(v___x_3776_, 4, v___f_3783_);
lean_ctor_set(v___x_3776_, 3, v___f_3784_);
lean_ctor_set(v___x_3776_, 2, v___f_3785_);
lean_ctor_set(v___x_3776_, 1, v___f_3778_);
lean_ctor_set(v___x_3776_, 0, v___x_3782_);
v___x_3787_ = v___x_3776_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3782_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v___f_3778_);
lean_ctor_set(v_reuseFailAlloc_3849_, 2, v___f_3785_);
lean_ctor_set(v_reuseFailAlloc_3849_, 3, v___f_3784_);
lean_ctor_set(v_reuseFailAlloc_3849_, 4, v___f_3783_);
v___x_3787_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
lean_object* v___x_3789_; 
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 1, v___f_3779_);
lean_ctor_set(v___x_3769_, 0, v___x_3787_);
v___x_3789_ = v___x_3769_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3787_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v___f_3779_);
v___x_3789_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3790_; lean_object* v_toApplicative_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3846_; 
v___x_3790_ = l_ReaderT_instMonad___redArg(v___x_3789_);
v_toApplicative_3791_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3846_ == 0)
{
lean_object* v_unused_3847_; 
v_unused_3847_ = lean_ctor_get(v___x_3790_, 1);
lean_dec(v_unused_3847_);
v___x_3793_ = v___x_3790_;
v_isShared_3794_ = v_isSharedCheck_3846_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_toApplicative_3791_);
lean_dec(v___x_3790_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3846_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v_toFunctor_3795_; lean_object* v_toSeq_3796_; lean_object* v_toSeqLeft_3797_; lean_object* v_toSeqRight_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3844_; 
v_toFunctor_3795_ = lean_ctor_get(v_toApplicative_3791_, 0);
v_toSeq_3796_ = lean_ctor_get(v_toApplicative_3791_, 2);
v_toSeqLeft_3797_ = lean_ctor_get(v_toApplicative_3791_, 3);
v_toSeqRight_3798_ = lean_ctor_get(v_toApplicative_3791_, 4);
v_isSharedCheck_3844_ = !lean_is_exclusive(v_toApplicative_3791_);
if (v_isSharedCheck_3844_ == 0)
{
lean_object* v_unused_3845_; 
v_unused_3845_ = lean_ctor_get(v_toApplicative_3791_, 1);
lean_dec(v_unused_3845_);
v___x_3800_ = v_toApplicative_3791_;
v_isShared_3801_ = v_isSharedCheck_3844_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_toSeqRight_3798_);
lean_inc(v_toSeqLeft_3797_);
lean_inc(v_toSeq_3796_);
lean_inc(v_toFunctor_3795_);
lean_dec(v_toApplicative_3791_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3844_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___f_3802_; lean_object* v___f_3803_; lean_object* v___f_3804_; lean_object* v___f_3805_; lean_object* v___x_3806_; lean_object* v___f_3807_; lean_object* v___f_3808_; lean_object* v___f_3809_; lean_object* v___x_3811_; 
v___f_3802_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_3803_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_3795_);
v___f_3804_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_3804_, 0, v_toFunctor_3795_);
v___f_3805_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3805_, 0, v_toFunctor_3795_);
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___f_3804_);
lean_ctor_set(v___x_3806_, 1, v___f_3805_);
v___f_3807_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3807_, 0, v_toSeqRight_3798_);
v___f_3808_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_3808_, 0, v_toSeqLeft_3797_);
v___f_3809_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3809_, 0, v_toSeq_3796_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 4, v___f_3807_);
lean_ctor_set(v___x_3800_, 3, v___f_3808_);
lean_ctor_set(v___x_3800_, 2, v___f_3809_);
lean_ctor_set(v___x_3800_, 1, v___f_3802_);
lean_ctor_set(v___x_3800_, 0, v___x_3806_);
v___x_3811_ = v___x_3800_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___f_3802_);
lean_ctor_set(v_reuseFailAlloc_3843_, 2, v___f_3809_);
lean_ctor_set(v_reuseFailAlloc_3843_, 3, v___f_3808_);
lean_ctor_set(v_reuseFailAlloc_3843_, 4, v___f_3807_);
v___x_3811_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3813_; 
if (v_isShared_3794_ == 0)
{
lean_ctor_set(v___x_3793_, 1, v___f_3803_);
lean_ctor_set(v___x_3793_, 0, v___x_3811_);
v___x_3813_ = v___x_3793_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3811_);
lean_ctor_set(v_reuseFailAlloc_3842_, 1, v___f_3803_);
v___x_3813_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3814_ = lean_array_get_size(v_acc_3759_);
v___x_3815_ = lean_array_get_size(v_declInfos_3755_);
v___x_3816_ = lean_nat_dec_lt(v___x_3814_, v___x_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; 
lean_dec_ref(v___x_3813_);
lean_dec(v_inst_3758_);
lean_dec_ref(v_declInfos_3755_);
v___x_3817_ = lean_apply_6(v_k_3756_, v_acc_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, lean_box(0));
return v___x_3817_;
}
else
{
lean_object* v___f_3818_; lean_object* v___x_3819_; uint8_t v___x_3820_; lean_object* v___f_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v_snd_3826_; lean_object* v_fst_3827_; lean_object* v_fst_3828_; lean_object* v_snd_3829_; lean_object* v___x_3830_; 
v___f_3818_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_3818_, 0, v___x_3813_);
v___x_3819_ = lean_box(0);
v___x_3820_ = 0;
v___f_3821_ = lean_alloc_closure((void*)(l_Pi_instInhabited___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3821_, 0, v___f_3818_);
v___x_3822_ = lean_box(v___x_3820_);
v___x_3823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3823_, 0, v___x_3822_);
lean_ctor_set(v___x_3823_, 1, v___f_3821_);
v___x_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3819_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_array_get_borrowed(v___x_3824_, v_declInfos_3755_, v___x_3814_);
v_snd_3826_ = lean_ctor_get(v___x_3825_, 1);
v_fst_3827_ = lean_ctor_get(v___x_3825_, 0);
lean_inc(v_fst_3827_);
v_fst_3828_ = lean_ctor_get(v_snd_3826_, 0);
v_snd_3829_ = lean_ctor_get(v_snd_3826_, 1);
lean_inc(v_snd_3829_);
lean_inc(v___y_3763_);
lean_inc_ref(v___y_3762_);
lean_inc(v___y_3761_);
lean_inc_ref(v___y_3760_);
lean_inc_ref(v_acc_3759_);
v___x_3830_ = lean_apply_6(v_snd_3829_, v_acc_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, lean_box(0));
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v_a_3831_; uint8_t v___x_3832_; lean_object* v___x_3833_; 
v_a_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_a_3831_);
lean_dec_ref(v___x_3830_);
v___x_3832_ = lean_unbox(v_fst_3828_);
v___x_3833_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(v_acc_3759_, v_declInfos_3755_, v_k_3756_, v_kind_3757_, v_inst_3758_, v_fst_3827_, v___x_3832_, v_a_3831_, v_kind_3757_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_);
return v___x_3833_;
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v_fst_3827_);
lean_dec(v___y_3763_);
lean_dec_ref(v___y_3762_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec_ref(v_acc_3759_);
lean_dec(v_inst_3758_);
lean_dec_ref(v_k_3756_);
lean_dec_ref(v_declInfos_3755_);
v_a_3834_ = lean_ctor_get(v___x_3830_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3830_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3830_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3830_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0(lean_object* v_acc_3854_, lean_object* v_declInfos_3855_, lean_object* v_k_3856_, uint8_t v_kind_3857_, lean_object* v_inst_3858_, lean_object* v_b_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; 
v___x_3865_ = lean_array_push(v_acc_3854_, v_b_3859_);
v___x_3866_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(v_declInfos_3855_, v_k_3856_, v_kind_3857_, v_inst_3858_, v___x_3865_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
return v___x_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_acc_3867_, lean_object* v_declInfos_3868_, lean_object* v_k_3869_, lean_object* v_kind_3870_, lean_object* v_inst_3871_, lean_object* v_name_3872_, lean_object* v_bi_3873_, lean_object* v_type_3874_, lean_object* v_kind_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
uint8_t v_kind_boxed_3881_; uint8_t v_bi_boxed_3882_; uint8_t v_kind_boxed_3883_; lean_object* v_res_3884_; 
v_kind_boxed_3881_ = lean_unbox(v_kind_3870_);
v_bi_boxed_3882_ = lean_unbox(v_bi_3873_);
v_kind_boxed_3883_ = lean_unbox(v_kind_3875_);
v_res_3884_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(v_acc_3867_, v_declInfos_3868_, v_k_3869_, v_kind_boxed_3881_, v_inst_3871_, v_name_3872_, v_bi_boxed_3882_, v_type_3874_, v_kind_boxed_3883_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_declInfos_3885_, lean_object* v_k_3886_, lean_object* v_kind_3887_, lean_object* v_inst_3888_, lean_object* v_acc_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
uint8_t v_kind_boxed_3895_; lean_object* v_res_3896_; 
v_kind_boxed_3895_ = lean_unbox(v_kind_3887_);
v_res_3896_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(v_declInfos_3885_, v_k_3886_, v_kind_boxed_3895_, v_inst_3888_, v_acc_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(lean_object* v_inst_3897_, lean_object* v_declInfos_3898_, lean_object* v_k_3899_, uint8_t v_kind_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_3907_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(v_declInfos_3898_, v_k_3899_, v_kind_3900_, v_inst_3897_, v___x_3906_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg___boxed(lean_object* v_inst_3908_, lean_object* v_declInfos_3909_, lean_object* v_k_3910_, lean_object* v_kind_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_){
_start:
{
uint8_t v_kind_boxed_3917_; lean_object* v_res_3918_; 
v_kind_boxed_3917_ = lean_unbox(v_kind_3911_);
v_res_3918_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(v_inst_3908_, v_declInfos_3909_, v_k_3910_, v_kind_boxed_3917_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
return v_res_3918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3919_, size_t v_i_3920_, lean_object* v_bs_3921_){
_start:
{
uint8_t v___x_3922_; 
v___x_3922_ = lean_usize_dec_lt(v_i_3920_, v_sz_3919_);
if (v___x_3922_ == 0)
{
return v_bs_3921_;
}
else
{
lean_object* v_v_3923_; lean_object* v_fst_3924_; lean_object* v_snd_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3941_; 
v_v_3923_ = lean_array_uget(v_bs_3921_, v_i_3920_);
v_fst_3924_ = lean_ctor_get(v_v_3923_, 0);
v_snd_3925_ = lean_ctor_get(v_v_3923_, 1);
v_isSharedCheck_3941_ = !lean_is_exclusive(v_v_3923_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3927_ = v_v_3923_;
v_isShared_3928_ = v_isSharedCheck_3941_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_snd_3925_);
lean_inc(v_fst_3924_);
lean_dec(v_v_3923_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3941_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v_bs_x27_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3934_; 
v___x_3929_ = lean_unsigned_to_nat(0u);
v_bs_x27_3930_ = lean_array_uset(v_bs_3921_, v_i_3920_, v___x_3929_);
v___x_3931_ = 0;
v___x_3932_ = lean_box(v___x_3931_);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 0, v___x_3932_);
v___x_3934_ = v___x_3927_;
goto v_reusejp_3933_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3932_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_snd_3925_);
v___x_3934_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3933_;
}
v_reusejp_3933_:
{
lean_object* v___x_3935_; size_t v___x_3936_; size_t v___x_3937_; lean_object* v___x_3938_; 
v___x_3935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3935_, 0, v_fst_3924_);
lean_ctor_set(v___x_3935_, 1, v___x_3934_);
v___x_3936_ = ((size_t)1ULL);
v___x_3937_ = lean_usize_add(v_i_3920_, v___x_3936_);
v___x_3938_ = lean_array_uset(v_bs_x27_3930_, v_i_3920_, v___x_3935_);
v_i_3920_ = v___x_3937_;
v_bs_3921_ = v___x_3938_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3942_, lean_object* v_i_3943_, lean_object* v_bs_3944_){
_start:
{
size_t v_sz_boxed_3945_; size_t v_i_boxed_3946_; lean_object* v_res_3947_; 
v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3942_);
lean_dec(v_sz_3942_);
v_i_boxed_3946_ = lean_unbox_usize(v_i_3943_);
lean_dec(v_i_3943_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3945_, v_i_boxed_3946_, v_bs_3944_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(lean_object* v_inst_3948_, lean_object* v_declInfos_3949_, lean_object* v_k_3950_, uint8_t v_kind_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
size_t v_sz_3957_; size_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_sz_3957_ = lean_array_size(v_declInfos_3949_);
v___x_3958_ = ((size_t)0ULL);
v___x_3959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3957_, v___x_3958_, v_declInfos_3949_);
v___x_3960_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(v_inst_3948_, v___x_3959_, v_k_3950_, v_kind_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg___boxed(lean_object* v_inst_3961_, lean_object* v_declInfos_3962_, lean_object* v_k_3963_, lean_object* v_kind_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
uint8_t v_kind_boxed_3970_; lean_object* v_res_3971_; 
v_kind_boxed_3970_ = lean_unbox(v_kind_3964_);
v_res_3971_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(v_inst_3961_, v_declInfos_3962_, v_k_3963_, v_kind_boxed_3970_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_);
return v_res_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3972_, lean_object* v_numParams_3973_, lean_object* v_a_3974_, lean_object* v___x_3975_, lean_object* v_compFields_3976_, lean_object* v___x_3977_, lean_object* v_val_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v_lower_3989_; lean_object* v_upper_3990_; lean_object* v___x_3999_; uint8_t v___x_4000_; 
v___x_3984_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3973_);
lean_inc_ref(v_paramsIndices_3972_);
v___x_3985_ = l_Array_toSubarray___redArg(v_paramsIndices_3972_, v___x_3984_, v_numParams_3973_);
v___x_3986_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_3987_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3985_, v___x_3986_);
v___x_3999_ = lean_array_get_size(v_paramsIndices_3972_);
v___x_4000_ = lean_nat_dec_le(v_numParams_3973_, v___x_3984_);
if (v___x_4000_ == 0)
{
v_lower_3989_ = v_numParams_3973_;
v_upper_3990_ = v___x_3999_;
goto v___jp_3988_;
}
else
{
lean_dec(v_numParams_3973_);
v_lower_3989_ = v___x_3984_;
v_upper_3990_ = v___x_3999_;
goto v___jp_3988_;
}
v___jp_3988_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___f_3993_; size_t v_sz_3994_; size_t v___x_3995_; lean_object* v___x_3996_; uint8_t v___x_3997_; lean_object* v___x_3998_; 
v___x_3991_ = l_Array_toSubarray___redArg(v_paramsIndices_3972_, v_lower_3989_, v_upper_3990_);
v___x_3992_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3991_, v___x_3986_);
lean_inc_ref(v_val_3978_);
lean_inc_ref(v___x_3992_);
lean_inc_ref(v_compFields_3976_);
lean_inc_ref(v___x_3987_);
v___f_3993_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3993_, 0, v_a_3974_);
lean_closure_set(v___f_3993_, 1, v___x_3975_);
lean_closure_set(v___f_3993_, 2, v___x_3987_);
lean_closure_set(v___f_3993_, 3, v_compFields_3976_);
lean_closure_set(v___f_3993_, 4, v___x_3992_);
lean_closure_set(v___f_3993_, 5, v_val_3978_);
v_sz_3994_ = lean_array_size(v_compFields_3976_);
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3987_, v___x_3992_, v_val_3978_, v_sz_3994_, v___x_3995_, v_compFields_3976_);
v___x_3997_ = 0;
v___x_3998_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(v___x_3977_, v___x_3996_, v___f_3993_, v___x_3997_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
return v___x_3998_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_4001_, lean_object* v_numParams_4002_, lean_object* v_a_4003_, lean_object* v___x_4004_, lean_object* v_compFields_4005_, lean_object* v___x_4006_, lean_object* v_val_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_4001_, v_numParams_4002_, v_a_4003_, v___x_4004_, v_compFields_4005_, v___x_4006_, v_val_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4014_, lean_object* v_b_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = lean_apply_6(v_k_4014_, v_b_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, lean_box(0));
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4022_, lean_object* v_b_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4022_, v_b_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
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
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4091_, lean_object* v_a_4092_, lean_object* v___x_4093_, lean_object* v_compFields_4094_, lean_object* v___x_4095_, lean_object* v_name_4096_, lean_object* v_paramsIndices_4097_, lean_object* v_x_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_){
_start:
{
lean_object* v___f_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_inc(v___x_4093_);
lean_inc_ref(v_paramsIndices_4097_);
v___f_4104_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 12, 6);
lean_closure_set(v___f_4104_, 0, v_paramsIndices_4097_);
lean_closure_set(v___f_4104_, 1, v_numParams_4091_);
lean_closure_set(v___f_4104_, 2, v_a_4092_);
lean_closure_set(v___f_4104_, 3, v___x_4093_);
lean_closure_set(v___f_4104_, 4, v_compFields_4094_);
lean_closure_set(v___f_4104_, 5, v___x_4095_);
v___x_4105_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4106_ = l_Lean_mkConst(v_name_4096_, v___x_4093_);
v___x_4107_ = l_Lean_mkAppN(v___x_4106_, v_paramsIndices_4097_);
lean_dec_ref(v_paramsIndices_4097_);
v___x_4108_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4105_, v___x_4107_, v___f_4104_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4109_, lean_object* v_a_4110_, lean_object* v___x_4111_, lean_object* v_compFields_4112_, lean_object* v___x_4113_, lean_object* v_name_4114_, lean_object* v_paramsIndices_4115_, lean_object* v_x_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4109_, v_a_4110_, v___x_4111_, v_compFields_4112_, v___x_4113_, v_name_4114_, v_paramsIndices_4115_, v_x_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec_ref(v_x_4116_);
return v_res_4122_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4125_ = l_Lean_stringToMessageData(v___x_4124_);
return v___x_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4126_, lean_object* v_compFields_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_){
_start:
{
lean_object* v___x_4133_; 
v___x_4133_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4126_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
if (lean_obj_tag(v___x_4133_) == 0)
{
lean_object* v_a_4134_; lean_object* v_toConstantVal_4135_; lean_object* v_numParams_4136_; lean_object* v_ctors_4137_; lean_object* v___x_4138_; lean_object* v___y_4140_; lean_object* v___y_4141_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v___x_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; 
v_a_4134_ = lean_ctor_get(v___x_4133_, 0);
lean_inc(v_a_4134_);
lean_dec_ref(v___x_4133_);
v_toConstantVal_4135_ = lean_ctor_get(v_a_4134_, 0);
v_numParams_4136_ = lean_ctor_get(v_a_4134_, 1);
lean_inc(v_numParams_4136_);
v_ctors_4137_ = lean_ctor_get(v_a_4134_, 4);
v___x_4138_ = lean_box(0);
v___x_4152_ = l_List_lengthTR___redArg(v_ctors_4137_);
v___x_4153_ = lean_unsigned_to_nat(2u);
v___x_4154_ = lean_nat_dec_lt(v___x_4152_, v___x_4153_);
lean_dec(v___x_4152_);
if (v___x_4154_ == 0)
{
v___y_4140_ = v_a_4128_;
v___y_4141_ = v_a_4129_;
v___y_4142_ = v_a_4130_;
v___y_4143_ = v_a_4131_;
goto v___jp_4139_;
}
else
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec(v_numParams_4136_);
lean_dec(v_a_4134_);
lean_dec_ref(v_compFields_4127_);
v___x_4155_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4156_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4155_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
lean_dec(v_a_4129_);
lean_dec_ref(v_a_4128_);
return v___x_4156_;
}
v___jp_4139_:
{
lean_object* v_name_4144_; lean_object* v_levelParams_4145_; lean_object* v_type_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___f_4149_; uint8_t v___x_4150_; lean_object* v___x_4151_; 
v_name_4144_ = lean_ctor_get(v_toConstantVal_4135_, 0);
lean_inc(v_name_4144_);
v_levelParams_4145_ = lean_ctor_get(v_toConstantVal_4135_, 1);
v_type_4146_ = lean_ctor_get(v_toConstantVal_4135_, 2);
lean_inc_ref(v_type_4146_);
v___x_4147_ = lean_box(0);
lean_inc(v_levelParams_4145_);
v___x_4148_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4145_, v___x_4147_);
v___f_4149_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 13, 6);
lean_closure_set(v___f_4149_, 0, v_numParams_4136_);
lean_closure_set(v___f_4149_, 1, v_a_4134_);
lean_closure_set(v___f_4149_, 2, v___x_4148_);
lean_closure_set(v___f_4149_, 3, v_compFields_4127_);
lean_closure_set(v___f_4149_, 4, v___x_4138_);
lean_closure_set(v___f_4149_, 5, v_name_4144_);
v___x_4150_ = 0;
v___x_4151_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4146_, v___f_4149_, v___x_4150_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_);
return v___x_4151_;
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
lean_dec(v_a_4129_);
lean_dec_ref(v_a_4128_);
lean_dec_ref(v_compFields_4127_);
v_a_4157_ = lean_ctor_get(v___x_4133_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4133_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___x_4133_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___x_4133_);
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
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_00_u03b1_4173_, lean_object* v_inst_4174_, lean_object* v_declInfos_4175_, lean_object* v_k_4176_, uint8_t v_kind_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v___x_4183_; 
v___x_4183_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(v_inst_4174_, v_declInfos_4175_, v_k_4176_, v_kind_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_);
return v___x_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_00_u03b1_4184_, lean_object* v_inst_4185_, lean_object* v_declInfos_4186_, lean_object* v_k_4187_, lean_object* v_kind_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
uint8_t v_kind_boxed_4194_; lean_object* v_res_4195_; 
v_kind_boxed_4194_ = lean_unbox(v_kind_4188_);
v_res_4195_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_00_u03b1_4184_, v_inst_4185_, v_declInfos_4186_, v_k_4187_, v_kind_boxed_4194_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4196_, lean_object* v_name_4197_, uint8_t v_bi_4198_, lean_object* v_type_4199_, lean_object* v_k_4200_, uint8_t v_kind_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4197_, v_bi_4198_, v_type_4199_, v_k_4200_, v_kind_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4208_, lean_object* v_name_4209_, lean_object* v_bi_4210_, lean_object* v_type_4211_, lean_object* v_k_4212_, lean_object* v_kind_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_){
_start:
{
uint8_t v_bi_boxed_4219_; uint8_t v_kind_boxed_4220_; lean_object* v_res_4221_; 
v_bi_boxed_4219_ = lean_unbox(v_bi_4210_);
v_kind_boxed_4220_ = lean_unbox(v_kind_4213_);
v_res_4221_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4208_, v_name_4209_, v_bi_boxed_4219_, v_type_4211_, v_k_4212_, v_kind_boxed_4220_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_);
return v_res_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4222_, lean_object* v_name_4223_, lean_object* v_type_4224_, lean_object* v_k_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4223_, v_type_4224_, v_k_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4232_, lean_object* v_name_4233_, lean_object* v_type_4234_, lean_object* v_k_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4232_, v_name_4233_, v_type_4234_, v_k_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_00_u03b1_4242_, lean_object* v_inst_4243_, lean_object* v_declInfos_4244_, lean_object* v_k_4245_, uint8_t v_kind_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(v_inst_4243_, v_declInfos_4244_, v_k_4245_, v_kind_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4253_, lean_object* v_inst_4254_, lean_object* v_declInfos_4255_, lean_object* v_k_4256_, lean_object* v_kind_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_){
_start:
{
uint8_t v_kind_boxed_4263_; lean_object* v_res_4264_; 
v_kind_boxed_4263_ = lean_unbox(v_kind_4257_);
v_res_4264_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_00_u03b1_4253_, v_inst_4254_, v_declInfos_4255_, v_k_4256_, v_kind_boxed_4263_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b1_4265_, lean_object* v_acc_4266_, lean_object* v_declInfos_4267_, lean_object* v_k_4268_, uint8_t v_kind_4269_, lean_object* v_inst_4270_, lean_object* v_name_4271_, uint8_t v_bi_4272_, lean_object* v_type_4273_, uint8_t v_kind_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(v_acc_4266_, v_declInfos_4267_, v_k_4268_, v_kind_4269_, v_inst_4270_, v_name_4271_, v_bi_4272_, v_type_4273_, v_kind_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_4281_, lean_object* v_acc_4282_, lean_object* v_declInfos_4283_, lean_object* v_k_4284_, lean_object* v_kind_4285_, lean_object* v_inst_4286_, lean_object* v_name_4287_, lean_object* v_bi_4288_, lean_object* v_type_4289_, lean_object* v_kind_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
uint8_t v_kind_boxed_4296_; uint8_t v_bi_boxed_4297_; uint8_t v_kind_boxed_4298_; lean_object* v_res_4299_; 
v_kind_boxed_4296_ = lean_unbox(v_kind_4285_);
v_bi_boxed_4297_ = lean_unbox(v_bi_4288_);
v_kind_boxed_4298_ = lean_unbox(v_kind_4290_);
v_res_4299_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_00_u03b1_4281_, v_acc_4282_, v_declInfos_4283_, v_k_4284_, v_kind_boxed_4296_, v_inst_4286_, v_name_4287_, v_bi_boxed_4297_, v_type_4289_, v_kind_boxed_4298_, v___y_4291_, v___y_4292_, v___y_4293_, v___y_4294_);
return v_res_4299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_4300_, lean_object* v_declInfos_4301_, lean_object* v_k_4302_, uint8_t v_kind_4303_, lean_object* v_inst_4304_, lean_object* v_acc_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v___x_4311_; 
v___x_4311_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(v_declInfos_4301_, v_k_4302_, v_kind_4303_, v_inst_4304_, v_acc_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4312_, lean_object* v_declInfos_4313_, lean_object* v_k_4314_, lean_object* v_kind_4315_, lean_object* v_inst_4316_, lean_object* v_acc_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
uint8_t v_kind_boxed_4323_; lean_object* v_res_4324_; 
v_kind_boxed_4323_ = lean_unbox(v_kind_4315_);
v_res_4324_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_00_u03b1_4312_, v_declInfos_4313_, v_k_4314_, v_kind_boxed_4323_, v_inst_4316_, v_acc_4317_, v___y_4318_, v___y_4319_, v___y_4320_, v___y_4321_);
return v_res_4324_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4325_, size_t v_sz_4326_, size_t v_i_4327_, lean_object* v_b_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v_a_4332_; uint8_t v___x_4336_; 
v___x_4336_ = lean_usize_dec_lt(v_i_4327_, v_sz_4326_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; 
v___x_4337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4337_, 0, v_b_4328_);
return v___x_4337_;
}
else
{
lean_object* v___x_4338_; lean_object* v_env_4339_; lean_object* v_a_4340_; uint8_t v___x_4341_; 
v___x_4338_ = lean_st_ref_get(v___y_4329_);
v_env_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc_ref(v_env_4339_);
lean_dec(v___x_4338_);
v_a_4340_ = lean_array_uget_borrowed(v_as_4325_, v_i_4327_);
lean_inc(v_a_4340_);
v___x_4341_ = l_Lean_isExtern(v_env_4339_, v_a_4340_);
if (v___x_4341_ == 0)
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4342_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4340_);
v___x_4343_ = l_Lean_Name_append(v_a_4340_, v___x_4342_);
v___x_4344_ = lean_array_push(v_b_4328_, v___x_4343_);
v_a_4332_ = v___x_4344_;
goto v___jp_4331_;
}
else
{
v_a_4332_ = v_b_4328_;
goto v___jp_4331_;
}
}
v___jp_4331_:
{
size_t v___x_4333_; size_t v___x_4334_; 
v___x_4333_ = ((size_t)1ULL);
v___x_4334_ = lean_usize_add(v_i_4327_, v___x_4333_);
v_i_4327_ = v___x_4334_;
v_b_4328_ = v_a_4332_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4345_, lean_object* v_sz_4346_, lean_object* v_i_4347_, lean_object* v_b_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
size_t v_sz_boxed_4351_; size_t v_i_boxed_4352_; lean_object* v_res_4353_; 
v_sz_boxed_4351_ = lean_unbox_usize(v_sz_4346_);
lean_dec(v_sz_4346_);
v_i_boxed_4352_ = lean_unbox_usize(v_i_4347_);
lean_dec(v_i_4347_);
v_res_4353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4345_, v_sz_boxed_4351_, v_i_boxed_4352_, v_b_4348_, v___y_4349_);
lean_dec(v___y_4349_);
lean_dec_ref(v_as_4345_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4354_, lean_object* v_b_4355_){
_start:
{
if (lean_obj_tag(v_as_x27_4354_) == 0)
{
lean_object* v___x_4357_; 
v___x_4357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4357_, 0, v_b_4355_);
return v___x_4357_;
}
else
{
lean_object* v_head_4358_; lean_object* v_tail_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v_head_4358_ = lean_ctor_get(v_as_x27_4354_, 0);
lean_inc(v_head_4358_);
v_tail_4359_ = lean_ctor_get(v_as_x27_4354_, 1);
lean_inc(v_tail_4359_);
lean_dec_ref(v_as_x27_4354_);
v___x_4360_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4361_ = l_Lean_Name_append(v_head_4358_, v___x_4360_);
v___x_4362_ = lean_array_push(v_b_4355_, v___x_4361_);
v_as_x27_4354_ = v_tail_4359_;
v_b_4355_ = v___x_4362_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4364_, lean_object* v_b_4365_, lean_object* v___y_4366_){
_start:
{
lean_object* v_res_4367_; 
v_res_4367_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4364_, v_b_4365_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4368_, size_t v_sz_4369_, size_t v_i_4370_, lean_object* v_b_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
uint8_t v___x_4377_; 
v___x_4377_ = lean_usize_dec_lt(v_i_4370_, v_sz_4369_);
if (v___x_4377_ == 0)
{
lean_object* v___x_4378_; 
v___x_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4378_, 0, v_b_4371_);
return v___x_4378_;
}
else
{
lean_object* v_a_4379_; lean_object* v_fst_4380_; lean_object* v_snd_4381_; lean_object* v___x_4382_; 
v_a_4379_ = lean_array_uget_borrowed(v_as_4368_, v_i_4370_);
v_fst_4380_ = lean_ctor_get(v_a_4379_, 0);
v_snd_4381_ = lean_ctor_get(v_a_4379_, 1);
lean_inc(v_fst_4380_);
v___x_4382_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4380_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v_ctors_4384_; lean_object* v___x_4385_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_a_4383_);
lean_dec_ref(v___x_4382_);
v_ctors_4384_ = lean_ctor_get(v_a_4383_, 4);
lean_inc(v_ctors_4384_);
lean_dec(v_a_4383_);
v___x_4385_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4384_, v_b_4371_);
if (lean_obj_tag(v___x_4385_) == 0)
{
lean_object* v_a_4386_; size_t v_sz_4387_; size_t v___x_4388_; lean_object* v___x_4389_; 
v_a_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc(v_a_4386_);
lean_dec_ref(v___x_4385_);
v_sz_4387_ = lean_array_size(v_snd_4381_);
v___x_4388_ = ((size_t)0ULL);
v___x_4389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4381_, v_sz_4387_, v___x_4388_, v_a_4386_, v___y_4375_);
if (lean_obj_tag(v___x_4389_) == 0)
{
lean_object* v_a_4390_; size_t v___x_4391_; size_t v___x_4392_; 
v_a_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc(v_a_4390_);
lean_dec_ref(v___x_4389_);
v___x_4391_ = ((size_t)1ULL);
v___x_4392_ = lean_usize_add(v_i_4370_, v___x_4391_);
v_i_4370_ = v___x_4392_;
v_b_4371_ = v_a_4390_;
goto _start;
}
else
{
return v___x_4389_;
}
}
else
{
return v___x_4385_;
}
}
else
{
lean_object* v_a_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4401_; 
lean_dec_ref(v_b_4371_);
v_a_4394_ = lean_ctor_get(v___x_4382_, 0);
v_isSharedCheck_4401_ = !lean_is_exclusive(v___x_4382_);
if (v_isSharedCheck_4401_ == 0)
{
v___x_4396_ = v___x_4382_;
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_a_4394_);
lean_dec(v___x_4382_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4401_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4399_; 
if (v_isShared_4397_ == 0)
{
v___x_4399_ = v___x_4396_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4400_; 
v_reuseFailAlloc_4400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
v___x_4399_ = v_reuseFailAlloc_4400_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
return v___x_4399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4402_, lean_object* v_sz_4403_, lean_object* v_i_4404_, lean_object* v_b_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
size_t v_sz_boxed_4411_; size_t v_i_boxed_4412_; lean_object* v_res_4413_; 
v_sz_boxed_4411_ = lean_unbox_usize(v_sz_4403_);
lean_dec(v_sz_4403_);
v_i_boxed_4412_ = lean_unbox_usize(v_i_4404_);
lean_dec(v_i_4404_);
v_res_4413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4402_, v_sz_boxed_4411_, v_i_boxed_4412_, v_b_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec_ref(v_as_4402_);
return v_res_4413_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v___y_4421_, uint8_t v_suppressElabErrors_4422_, lean_object* v_x_4423_){
_start:
{
if (lean_obj_tag(v_x_4423_) == 1)
{
lean_object* v_pre_4424_; 
v_pre_4424_ = lean_ctor_get(v_x_4423_, 0);
switch(lean_obj_tag(v_pre_4424_))
{
case 1:
{
lean_object* v_pre_4425_; 
v_pre_4425_ = lean_ctor_get(v_pre_4424_, 0);
switch(lean_obj_tag(v_pre_4425_))
{
case 0:
{
lean_object* v_str_4426_; lean_object* v_str_4427_; lean_object* v___x_4428_; uint8_t v___x_4429_; 
v_str_4426_ = lean_ctor_get(v_x_4423_, 1);
v_str_4427_ = lean_ctor_get(v_pre_4424_, 1);
v___x_4428_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4429_ = lean_string_dec_eq(v_str_4427_, v___x_4428_);
if (v___x_4429_ == 0)
{
lean_object* v___x_4430_; uint8_t v___x_4431_; 
v___x_4430_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4431_ = lean_string_dec_eq(v_str_4427_, v___x_4430_);
if (v___x_4431_ == 0)
{
return v___y_4421_;
}
else
{
lean_object* v___x_4432_; uint8_t v___x_4433_; 
v___x_4432_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4433_ = lean_string_dec_eq(v_str_4426_, v___x_4432_);
if (v___x_4433_ == 0)
{
return v___y_4421_;
}
else
{
return v_suppressElabErrors_4422_;
}
}
}
else
{
lean_object* v___x_4434_; uint8_t v___x_4435_; 
v___x_4434_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4435_ = lean_string_dec_eq(v_str_4426_, v___x_4434_);
if (v___x_4435_ == 0)
{
return v___y_4421_;
}
else
{
return v_suppressElabErrors_4422_;
}
}
}
case 1:
{
lean_object* v_pre_4436_; 
v_pre_4436_ = lean_ctor_get(v_pre_4425_, 0);
if (lean_obj_tag(v_pre_4436_) == 0)
{
lean_object* v_str_4437_; lean_object* v_str_4438_; lean_object* v_str_4439_; lean_object* v___x_4440_; uint8_t v___x_4441_; 
v_str_4437_ = lean_ctor_get(v_x_4423_, 1);
v_str_4438_ = lean_ctor_get(v_pre_4424_, 1);
v_str_4439_ = lean_ctor_get(v_pre_4425_, 1);
v___x_4440_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4441_ = lean_string_dec_eq(v_str_4439_, v___x_4440_);
if (v___x_4441_ == 0)
{
return v___y_4421_;
}
else
{
lean_object* v___x_4442_; uint8_t v___x_4443_; 
v___x_4442_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4443_ = lean_string_dec_eq(v_str_4438_, v___x_4442_);
if (v___x_4443_ == 0)
{
return v___y_4421_;
}
else
{
lean_object* v___x_4444_; uint8_t v___x_4445_; 
v___x_4444_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4445_ = lean_string_dec_eq(v_str_4437_, v___x_4444_);
if (v___x_4445_ == 0)
{
return v___y_4421_;
}
else
{
return v_suppressElabErrors_4422_;
}
}
}
}
else
{
return v___y_4421_;
}
}
default: 
{
return v___y_4421_;
}
}
}
case 0:
{
lean_object* v_str_4446_; lean_object* v___x_4447_; uint8_t v___x_4448_; 
v_str_4446_ = lean_ctor_get(v_x_4423_, 1);
v___x_4447_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4448_ = lean_string_dec_eq(v_str_4446_, v___x_4447_);
if (v___x_4448_ == 0)
{
return v___y_4421_;
}
else
{
return v_suppressElabErrors_4422_;
}
}
default: 
{
return v___y_4421_;
}
}
}
else
{
return v___y_4421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v___y_4449_, lean_object* v_suppressElabErrors_4450_, lean_object* v_x_4451_){
_start:
{
uint8_t v___y_7631__boxed_4452_; uint8_t v_suppressElabErrors_boxed_4453_; uint8_t v_res_4454_; lean_object* v_r_4455_; 
v___y_7631__boxed_4452_ = lean_unbox(v___y_4449_);
v_suppressElabErrors_boxed_4453_ = lean_unbox(v_suppressElabErrors_4450_);
v_res_4454_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v___y_7631__boxed_4452_, v_suppressElabErrors_boxed_4453_, v_x_4451_);
lean_dec(v_x_4451_);
v_r_4455_ = lean_box(v_res_4454_);
return v_r_4455_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4456_, lean_object* v_opt_4457_){
_start:
{
lean_object* v_name_4458_; lean_object* v_defValue_4459_; lean_object* v_map_4460_; lean_object* v___x_4461_; 
v_name_4458_ = lean_ctor_get(v_opt_4457_, 0);
v_defValue_4459_ = lean_ctor_get(v_opt_4457_, 1);
v_map_4460_ = lean_ctor_get(v_opts_4456_, 0);
v___x_4461_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4460_, v_name_4458_);
if (lean_obj_tag(v___x_4461_) == 0)
{
uint8_t v___x_4462_; 
v___x_4462_ = lean_unbox(v_defValue_4459_);
return v___x_4462_;
}
else
{
lean_object* v_val_4463_; 
v_val_4463_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_val_4463_);
lean_dec_ref(v___x_4461_);
if (lean_obj_tag(v_val_4463_) == 1)
{
uint8_t v_v_4464_; 
v_v_4464_ = lean_ctor_get_uint8(v_val_4463_, 0);
lean_dec_ref(v_val_4463_);
return v_v_4464_;
}
else
{
uint8_t v___x_4465_; 
lean_dec(v_val_4463_);
v___x_4465_ = lean_unbox(v_defValue_4459_);
return v___x_4465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4466_, lean_object* v_opt_4467_){
_start:
{
uint8_t v_res_4468_; lean_object* v_r_4469_; 
v_res_4468_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4466_, v_opt_4467_);
lean_dec_ref(v_opt_4467_);
lean_dec_ref(v_opts_4466_);
v_r_4469_ = lean_box(v_res_4468_);
return v_r_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4471_, lean_object* v_msgData_4472_, uint8_t v_severity_4473_, uint8_t v_isSilent_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v___y_4481_; lean_object* v___y_4482_; uint8_t v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; uint8_t v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4517_; uint8_t v___y_4518_; lean_object* v___y_4519_; uint8_t v___y_4520_; uint8_t v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; lean_object* v___y_4524_; lean_object* v___y_4542_; lean_object* v___y_4543_; uint8_t v___y_4544_; lean_object* v___y_4545_; uint8_t v___y_4546_; uint8_t v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4553_; lean_object* v___y_4554_; uint8_t v___y_4555_; uint8_t v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; uint8_t v___y_4559_; uint8_t v___x_4564_; lean_object* v___y_4566_; lean_object* v___y_4567_; uint8_t v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; uint8_t v___y_4571_; uint8_t v___y_4572_; uint8_t v___y_4574_; uint8_t v___x_4589_; 
v___x_4564_ = 2;
v___x_4589_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4473_, v___x_4564_);
if (v___x_4589_ == 0)
{
v___y_4574_ = v___x_4589_;
goto v___jp_4573_;
}
else
{
uint8_t v___x_4590_; 
lean_inc_ref(v_msgData_4472_);
v___x_4590_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4472_);
v___y_4574_ = v___x_4590_;
goto v___jp_4573_;
}
v___jp_4480_:
{
lean_object* v___x_4490_; lean_object* v_currNamespace_4491_; lean_object* v_openDecls_4492_; lean_object* v_env_4493_; lean_object* v_nextMacroScope_4494_; lean_object* v_ngen_4495_; lean_object* v_auxDeclNGen_4496_; lean_object* v_traceState_4497_; lean_object* v_cache_4498_; lean_object* v_messages_4499_; lean_object* v_infoState_4500_; lean_object* v_snapshotTasks_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4515_; 
v___x_4490_ = lean_st_ref_take(v___y_4489_);
v_currNamespace_4491_ = lean_ctor_get(v___y_4488_, 6);
lean_inc(v_currNamespace_4491_);
v_openDecls_4492_ = lean_ctor_get(v___y_4488_, 7);
lean_inc(v_openDecls_4492_);
lean_dec_ref(v___y_4488_);
v_env_4493_ = lean_ctor_get(v___x_4490_, 0);
v_nextMacroScope_4494_ = lean_ctor_get(v___x_4490_, 1);
v_ngen_4495_ = lean_ctor_get(v___x_4490_, 2);
v_auxDeclNGen_4496_ = lean_ctor_get(v___x_4490_, 3);
v_traceState_4497_ = lean_ctor_get(v___x_4490_, 4);
v_cache_4498_ = lean_ctor_get(v___x_4490_, 5);
v_messages_4499_ = lean_ctor_get(v___x_4490_, 6);
v_infoState_4500_ = lean_ctor_get(v___x_4490_, 7);
v_snapshotTasks_4501_ = lean_ctor_get(v___x_4490_, 8);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4503_ = v___x_4490_;
v_isShared_4504_ = v_isSharedCheck_4515_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_snapshotTasks_4501_);
lean_inc(v_infoState_4500_);
lean_inc(v_messages_4499_);
lean_inc(v_cache_4498_);
lean_inc(v_traceState_4497_);
lean_inc(v_auxDeclNGen_4496_);
lean_inc(v_ngen_4495_);
lean_inc(v_nextMacroScope_4494_);
lean_inc(v_env_4493_);
lean_dec(v___x_4490_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4515_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4505_, 0, v_currNamespace_4491_);
lean_ctor_set(v___x_4505_, 1, v_openDecls_4492_);
v___x_4506_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
lean_ctor_set(v___x_4506_, 1, v___y_4484_);
v___x_4507_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4507_, 0, v___y_4485_);
lean_ctor_set(v___x_4507_, 1, v___y_4482_);
lean_ctor_set(v___x_4507_, 2, v___y_4486_);
lean_ctor_set(v___x_4507_, 3, v___y_4481_);
lean_ctor_set(v___x_4507_, 4, v___x_4506_);
lean_ctor_set_uint8(v___x_4507_, sizeof(void*)*5, v___y_4487_);
lean_ctor_set_uint8(v___x_4507_, sizeof(void*)*5 + 1, v___y_4483_);
lean_ctor_set_uint8(v___x_4507_, sizeof(void*)*5 + 2, v_isSilent_4474_);
v___x_4508_ = l_Lean_MessageLog_add(v___x_4507_, v_messages_4499_);
if (v_isShared_4504_ == 0)
{
lean_ctor_set(v___x_4503_, 6, v___x_4508_);
v___x_4510_ = v___x_4503_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_env_4493_);
lean_ctor_set(v_reuseFailAlloc_4514_, 1, v_nextMacroScope_4494_);
lean_ctor_set(v_reuseFailAlloc_4514_, 2, v_ngen_4495_);
lean_ctor_set(v_reuseFailAlloc_4514_, 3, v_auxDeclNGen_4496_);
lean_ctor_set(v_reuseFailAlloc_4514_, 4, v_traceState_4497_);
lean_ctor_set(v_reuseFailAlloc_4514_, 5, v_cache_4498_);
lean_ctor_set(v_reuseFailAlloc_4514_, 6, v___x_4508_);
lean_ctor_set(v_reuseFailAlloc_4514_, 7, v_infoState_4500_);
lean_ctor_set(v_reuseFailAlloc_4514_, 8, v_snapshotTasks_4501_);
v___x_4510_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v___x_4511_ = lean_st_ref_set(v___y_4489_, v___x_4510_);
v___x_4512_ = lean_box(0);
v___x_4513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4513_, 0, v___x_4512_);
return v___x_4513_;
}
}
}
v___jp_4516_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4540_; 
v___x_4525_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4472_);
v___x_4526_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4525_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4529_ = v___x_4526_;
v_isShared_4530_ = v_isSharedCheck_4540_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4526_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4540_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
lean_inc_ref(v___y_4522_);
v___x_4531_ = l_Lean_FileMap_toPosition(v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
v___x_4532_ = l_Lean_FileMap_toPosition(v___y_4522_, v___y_4524_);
lean_dec(v___y_4524_);
v___x_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4532_);
v___x_4534_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4520_ == 0)
{
lean_del_object(v___x_4529_);
lean_dec_ref(v___y_4517_);
v___y_4481_ = v___x_4534_;
v___y_4482_ = v___x_4531_;
v___y_4483_ = v___y_4518_;
v___y_4484_ = v_a_4527_;
v___y_4485_ = v___y_4519_;
v___y_4486_ = v___x_4533_;
v___y_4487_ = v___y_4521_;
v___y_4488_ = v___y_4477_;
v___y_4489_ = v___y_4478_;
goto v___jp_4480_;
}
else
{
uint8_t v___x_4535_; 
lean_inc(v_a_4527_);
v___x_4535_ = l_Lean_MessageData_hasTag(v___y_4517_, v_a_4527_);
if (v___x_4535_ == 0)
{
lean_object* v___x_4536_; lean_object* v___x_4538_; 
lean_dec_ref(v___x_4533_);
lean_dec_ref(v___x_4531_);
lean_dec(v_a_4527_);
lean_dec_ref(v___y_4519_);
lean_dec_ref(v___y_4477_);
v___x_4536_ = lean_box(0);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4536_);
v___x_4538_ = v___x_4529_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
else
{
lean_del_object(v___x_4529_);
v___y_4481_ = v___x_4534_;
v___y_4482_ = v___x_4531_;
v___y_4483_ = v___y_4518_;
v___y_4484_ = v_a_4527_;
v___y_4485_ = v___y_4519_;
v___y_4486_ = v___x_4533_;
v___y_4487_ = v___y_4521_;
v___y_4488_ = v___y_4477_;
v___y_4489_ = v___y_4478_;
goto v___jp_4480_;
}
}
}
}
v___jp_4541_:
{
lean_object* v___x_4550_; 
v___x_4550_ = l_Lean_Syntax_getTailPos_x3f(v___y_4543_, v___y_4547_);
lean_dec(v___y_4543_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_inc(v___y_4549_);
v___y_4517_ = v___y_4542_;
v___y_4518_ = v___y_4544_;
v___y_4519_ = v___y_4545_;
v___y_4520_ = v___y_4546_;
v___y_4521_ = v___y_4547_;
v___y_4522_ = v___y_4548_;
v___y_4523_ = v___y_4549_;
v___y_4524_ = v___y_4549_;
goto v___jp_4516_;
}
else
{
lean_object* v_val_4551_; 
v_val_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_val_4551_);
lean_dec_ref(v___x_4550_);
v___y_4517_ = v___y_4542_;
v___y_4518_ = v___y_4544_;
v___y_4519_ = v___y_4545_;
v___y_4520_ = v___y_4546_;
v___y_4521_ = v___y_4547_;
v___y_4522_ = v___y_4548_;
v___y_4523_ = v___y_4549_;
v___y_4524_ = v_val_4551_;
goto v___jp_4516_;
}
}
v___jp_4552_:
{
lean_object* v_ref_4560_; lean_object* v___x_4561_; 
v_ref_4560_ = l_Lean_replaceRef(v_ref_4471_, v___y_4557_);
lean_dec(v___y_4557_);
v___x_4561_ = l_Lean_Syntax_getPos_x3f(v_ref_4560_, v___y_4556_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_object* v___x_4562_; 
v___x_4562_ = lean_unsigned_to_nat(0u);
v___y_4542_ = v___y_4553_;
v___y_4543_ = v_ref_4560_;
v___y_4544_ = v___y_4559_;
v___y_4545_ = v___y_4554_;
v___y_4546_ = v___y_4555_;
v___y_4547_ = v___y_4556_;
v___y_4548_ = v___y_4558_;
v___y_4549_ = v___x_4562_;
goto v___jp_4541_;
}
else
{
lean_object* v_val_4563_; 
v_val_4563_ = lean_ctor_get(v___x_4561_, 0);
lean_inc(v_val_4563_);
lean_dec_ref(v___x_4561_);
v___y_4542_ = v___y_4553_;
v___y_4543_ = v_ref_4560_;
v___y_4544_ = v___y_4559_;
v___y_4545_ = v___y_4554_;
v___y_4546_ = v___y_4555_;
v___y_4547_ = v___y_4556_;
v___y_4548_ = v___y_4558_;
v___y_4549_ = v_val_4563_;
goto v___jp_4541_;
}
}
v___jp_4565_:
{
if (v___y_4572_ == 0)
{
v___y_4553_ = v___y_4566_;
v___y_4554_ = v___y_4567_;
v___y_4555_ = v___y_4568_;
v___y_4556_ = v___y_4571_;
v___y_4557_ = v___y_4569_;
v___y_4558_ = v___y_4570_;
v___y_4559_ = v_severity_4473_;
goto v___jp_4552_;
}
else
{
v___y_4553_ = v___y_4566_;
v___y_4554_ = v___y_4567_;
v___y_4555_ = v___y_4568_;
v___y_4556_ = v___y_4571_;
v___y_4557_ = v___y_4569_;
v___y_4558_ = v___y_4570_;
v___y_4559_ = v___x_4564_;
goto v___jp_4552_;
}
}
v___jp_4573_:
{
if (v___y_4574_ == 0)
{
lean_object* v_fileName_4575_; lean_object* v_fileMap_4576_; lean_object* v_options_4577_; lean_object* v_ref_4578_; uint8_t v_suppressElabErrors_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___f_4582_; uint8_t v___x_4583_; uint8_t v___x_4584_; 
v_fileName_4575_ = lean_ctor_get(v___y_4477_, 0);
v_fileMap_4576_ = lean_ctor_get(v___y_4477_, 1);
v_options_4577_ = lean_ctor_get(v___y_4477_, 2);
v_ref_4578_ = lean_ctor_get(v___y_4477_, 5);
v_suppressElabErrors_4579_ = lean_ctor_get_uint8(v___y_4477_, sizeof(void*)*14 + 1);
v___x_4580_ = lean_box(v___y_4574_);
v___x_4581_ = lean_box(v_suppressElabErrors_4579_);
v___f_4582_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4582_, 0, v___x_4580_);
lean_closure_set(v___f_4582_, 1, v___x_4581_);
v___x_4583_ = 1;
v___x_4584_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4473_, v___x_4583_);
if (v___x_4584_ == 0)
{
lean_inc_ref(v_fileMap_4576_);
lean_inc(v_ref_4578_);
lean_inc_ref(v_fileName_4575_);
v___y_4566_ = v___f_4582_;
v___y_4567_ = v_fileName_4575_;
v___y_4568_ = v_suppressElabErrors_4579_;
v___y_4569_ = v_ref_4578_;
v___y_4570_ = v_fileMap_4576_;
v___y_4571_ = v___y_4574_;
v___y_4572_ = v___x_4584_;
goto v___jp_4565_;
}
else
{
lean_object* v___x_4585_; uint8_t v___x_4586_; 
v___x_4585_ = l_Lean_warningAsError;
v___x_4586_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4577_, v___x_4585_);
lean_inc_ref(v_fileMap_4576_);
lean_inc(v_ref_4578_);
lean_inc_ref(v_fileName_4575_);
v___y_4566_ = v___f_4582_;
v___y_4567_ = v_fileName_4575_;
v___y_4568_ = v_suppressElabErrors_4579_;
v___y_4569_ = v_ref_4578_;
v___y_4570_ = v_fileMap_4576_;
v___y_4571_ = v___y_4574_;
v___y_4572_ = v___x_4586_;
goto v___jp_4565_;
}
}
else
{
lean_object* v___x_4587_; lean_object* v___x_4588_; 
lean_dec_ref(v___y_4477_);
lean_dec_ref(v_msgData_4472_);
v___x_4587_ = lean_box(0);
v___x_4588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4588_, 0, v___x_4587_);
return v___x_4588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4591_, lean_object* v_msgData_4592_, lean_object* v_severity_4593_, lean_object* v_isSilent_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_, lean_object* v___y_4599_){
_start:
{
uint8_t v_severity_boxed_4600_; uint8_t v_isSilent_boxed_4601_; lean_object* v_res_4602_; 
v_severity_boxed_4600_ = lean_unbox(v_severity_4593_);
v_isSilent_boxed_4601_ = lean_unbox(v_isSilent_4594_);
v_res_4602_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4591_, v_msgData_4592_, v_severity_boxed_4600_, v_isSilent_boxed_4601_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
lean_dec(v___y_4598_);
lean_dec(v___y_4596_);
lean_dec_ref(v___y_4595_);
lean_dec(v_ref_4591_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4603_, uint8_t v_severity_4604_, uint8_t v_isSilent_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v_ref_4611_; lean_object* v___x_4612_; 
v_ref_4611_ = lean_ctor_get(v___y_4608_, 5);
lean_inc(v_ref_4611_);
v___x_4612_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4611_, v_msgData_4603_, v_severity_4604_, v_isSilent_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_);
lean_dec(v_ref_4611_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4613_, lean_object* v_severity_4614_, lean_object* v_isSilent_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
uint8_t v_severity_boxed_4621_; uint8_t v_isSilent_boxed_4622_; lean_object* v_res_4623_; 
v_severity_boxed_4621_ = lean_unbox(v_severity_4614_);
v_isSilent_boxed_4622_ = lean_unbox(v_isSilent_4615_);
v_res_4623_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4613_, v_severity_boxed_4621_, v_isSilent_boxed_4622_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
lean_dec(v___y_4619_);
lean_dec(v___y_4617_);
lean_dec_ref(v___y_4616_);
return v_res_4623_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_){
_start:
{
uint8_t v___x_4630_; uint8_t v___x_4631_; lean_object* v___x_4632_; 
v___x_4630_ = 2;
v___x_4631_ = 0;
v___x_4632_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4624_, v___x_4630_, v___x_4631_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
return v___x_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
lean_dec(v___y_4637_);
lean_dec(v___y_4635_);
lean_dec_ref(v___y_4634_);
return v_res_4639_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; 
v___x_4641_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4642_ = l_Lean_stringToMessageData(v___x_4641_);
return v___x_4642_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4644_; lean_object* v___x_4645_; 
v___x_4644_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4645_ = l_Lean_stringToMessageData(v___x_4644_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4646_, size_t v_sz_4647_, size_t v_i_4648_, lean_object* v_b_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_a_4656_; uint8_t v___x_4660_; 
v___x_4660_ = lean_usize_dec_lt(v_i_4648_, v_sz_4647_);
if (v___x_4660_ == 0)
{
lean_object* v___x_4661_; 
lean_dec_ref(v___y_4652_);
v___x_4661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4661_, 0, v_b_4649_);
return v___x_4661_;
}
else
{
lean_object* v___x_4662_; lean_object* v_env_4663_; lean_object* v___x_4664_; lean_object* v_a_4665_; lean_object* v___x_4666_; uint8_t v___x_4667_; 
v___x_4662_ = lean_st_ref_get(v___y_4653_);
v_env_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc_ref(v_env_4663_);
lean_dec(v___x_4662_);
v___x_4664_ = lean_box(0);
v_a_4665_ = lean_array_uget_borrowed(v_as_4646_, v_i_4648_);
v___x_4666_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4665_);
v___x_4667_ = l_Lean_TagAttribute_hasTag(v___x_4666_, v_env_4663_, v_a_4665_);
if (v___x_4667_ == 0)
{
lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; 
v___x_4668_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4665_);
v___x_4669_ = l_Lean_MessageData_ofName(v_a_4665_);
v___x_4670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4670_, 0, v___x_4668_);
lean_ctor_set(v___x_4670_, 1, v___x_4669_);
v___x_4671_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4672_, 0, v___x_4670_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
lean_inc_ref(v___y_4652_);
v___x_4673_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4672_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_dec_ref(v___x_4673_);
v_a_4656_ = v___x_4664_;
goto v___jp_4655_;
}
else
{
lean_dec_ref(v___y_4652_);
return v___x_4673_;
}
}
else
{
v_a_4656_ = v___x_4664_;
goto v___jp_4655_;
}
}
v___jp_4655_:
{
size_t v___x_4657_; size_t v___x_4658_; 
v___x_4657_ = ((size_t)1ULL);
v___x_4658_ = lean_usize_add(v_i_4648_, v___x_4657_);
v_i_4648_ = v___x_4658_;
v_b_4649_ = v_a_4656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4674_, lean_object* v_sz_4675_, lean_object* v_i_4676_, lean_object* v_b_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_){
_start:
{
size_t v_sz_boxed_4683_; size_t v_i_boxed_4684_; lean_object* v_res_4685_; 
v_sz_boxed_4683_ = lean_unbox_usize(v_sz_4675_);
lean_dec(v_sz_4675_);
v_i_boxed_4684_ = lean_unbox_usize(v_i_4676_);
lean_dec(v_i_4676_);
v_res_4685_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4674_, v_sz_boxed_4683_, v_i_boxed_4684_, v_b_4677_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
lean_dec(v___y_4681_);
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4678_);
lean_dec_ref(v_as_4674_);
return v_res_4685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4686_, size_t v_sz_4687_, size_t v_i_4688_, lean_object* v_b_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
uint8_t v___x_4695_; 
v___x_4695_ = lean_usize_dec_lt(v_i_4688_, v_sz_4687_);
if (v___x_4695_ == 0)
{
lean_object* v___x_4696_; 
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v_b_4689_);
return v___x_4696_;
}
else
{
lean_object* v_a_4697_; lean_object* v_fst_4698_; lean_object* v_snd_4699_; lean_object* v___x_4700_; size_t v_sz_4701_; size_t v___x_4702_; lean_object* v___x_4703_; 
v_a_4697_ = lean_array_uget_borrowed(v_as_4686_, v_i_4688_);
v_fst_4698_ = lean_ctor_get(v_a_4697_, 0);
v_snd_4699_ = lean_ctor_get(v_a_4697_, 1);
v___x_4700_ = lean_box(0);
v_sz_4701_ = lean_array_size(v_snd_4699_);
v___x_4702_ = ((size_t)0ULL);
lean_inc_ref(v___y_4692_);
v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4699_, v_sz_4701_, v___x_4702_, v___x_4700_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v___x_4704_; 
lean_dec_ref(v___x_4703_);
lean_inc(v___y_4693_);
lean_inc_ref(v___y_4692_);
lean_inc(v___y_4691_);
lean_inc_ref(v___y_4690_);
lean_inc(v_snd_4699_);
lean_inc(v_fst_4698_);
v___x_4704_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4698_, v_snd_4699_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_);
if (lean_obj_tag(v___x_4704_) == 0)
{
size_t v___x_4705_; size_t v___x_4706_; 
lean_dec_ref(v___x_4704_);
v___x_4705_ = ((size_t)1ULL);
v___x_4706_ = lean_usize_add(v_i_4688_, v___x_4705_);
v_i_4688_ = v___x_4706_;
v_b_4689_ = v___x_4700_;
goto _start;
}
else
{
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
return v___x_4704_;
}
}
else
{
lean_dec(v___y_4693_);
lean_dec_ref(v___y_4692_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
return v___x_4703_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4708_, lean_object* v_sz_4709_, lean_object* v_i_4710_, lean_object* v_b_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_){
_start:
{
size_t v_sz_boxed_4717_; size_t v_i_boxed_4718_; lean_object* v_res_4719_; 
v_sz_boxed_4717_ = lean_unbox_usize(v_sz_4709_);
lean_dec(v_sz_4709_);
v_i_boxed_4718_ = lean_unbox_usize(v_i_4710_);
lean_dec(v_i_4710_);
v_res_4719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4708_, v_sz_boxed_4717_, v_i_boxed_4718_, v_b_4711_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
lean_dec_ref(v_as_4708_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4720_, size_t v_i_4721_, lean_object* v_bs_4722_){
_start:
{
uint8_t v___x_4723_; 
v___x_4723_ = lean_usize_dec_lt(v_i_4721_, v_sz_4720_);
if (v___x_4723_ == 0)
{
return v_bs_4722_;
}
else
{
lean_object* v_v_4724_; lean_object* v_fst_4725_; lean_object* v___x_4726_; lean_object* v_bs_x27_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; size_t v___x_4731_; size_t v___x_4732_; lean_object* v___x_4733_; 
v_v_4724_ = lean_array_uget_borrowed(v_bs_4722_, v_i_4721_);
v_fst_4725_ = lean_ctor_get(v_v_4724_, 0);
lean_inc(v_fst_4725_);
v___x_4726_ = lean_unsigned_to_nat(0u);
v_bs_x27_4727_ = lean_array_uset(v_bs_4722_, v_i_4721_, v___x_4726_);
v___x_4728_ = l_Lean_mkCasesOnName(v_fst_4725_);
v___x_4729_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4730_ = l_Lean_Name_append(v___x_4728_, v___x_4729_);
v___x_4731_ = ((size_t)1ULL);
v___x_4732_ = lean_usize_add(v_i_4721_, v___x_4731_);
v___x_4733_ = lean_array_uset(v_bs_x27_4727_, v_i_4721_, v___x_4730_);
v_i_4721_ = v___x_4732_;
v_bs_4722_ = v___x_4733_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4735_, lean_object* v_i_4736_, lean_object* v_bs_4737_){
_start:
{
size_t v_sz_boxed_4738_; size_t v_i_boxed_4739_; lean_object* v_res_4740_; 
v_sz_boxed_4738_ = lean_unbox_usize(v_sz_4735_);
lean_dec(v_sz_4735_);
v_i_boxed_4739_ = lean_unbox_usize(v_i_4736_);
lean_dec(v_i_4736_);
v_res_4740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4738_, v_i_boxed_4739_, v_bs_4737_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_){
_start:
{
lean_object* v___x_4749_; size_t v_sz_4750_; size_t v___x_4751_; lean_object* v___x_4752_; 
v___x_4749_ = lean_box(0);
v_sz_4750_ = lean_array_size(v_computedFields_4743_);
v___x_4751_ = ((size_t)0ULL);
lean_inc(v_a_4747_);
lean_inc_ref(v_a_4746_);
lean_inc(v_a_4745_);
lean_inc_ref(v_a_4744_);
v___x_4752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4743_, v_sz_4750_, v___x_4751_, v___x_4749_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_object* v___x_4753_; uint8_t v___x_4754_; lean_object* v___x_4755_; 
lean_dec_ref(v___x_4752_);
lean_inc_ref(v_computedFields_4743_);
v___x_4753_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4750_, v___x_4751_, v_computedFields_4743_);
v___x_4754_ = 1;
lean_inc(v_a_4747_);
lean_inc_ref(v_a_4746_);
v___x_4755_ = l_Lean_compileDecls(v___x_4753_, v___x_4754_, v_a_4746_, v_a_4747_);
if (lean_obj_tag(v___x_4755_) == 0)
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
lean_dec_ref(v___x_4755_);
v___x_4756_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4757_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4743_, v_sz_4750_, v___x_4751_, v___x_4756_, v_a_4744_, v_a_4745_, v_a_4746_, v_a_4747_);
lean_dec(v_a_4745_);
lean_dec_ref(v_a_4744_);
lean_dec_ref(v_computedFields_4743_);
if (lean_obj_tag(v___x_4757_) == 0)
{
lean_object* v_a_4758_; lean_object* v___x_4759_; 
v_a_4758_ = lean_ctor_get(v___x_4757_, 0);
lean_inc(v_a_4758_);
lean_dec_ref(v___x_4757_);
v___x_4759_ = l_Lean_compileDecls(v_a_4758_, v___x_4754_, v_a_4746_, v_a_4747_);
return v___x_4759_;
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_dec(v_a_4747_);
lean_dec_ref(v_a_4746_);
v_a_4760_ = lean_ctor_get(v___x_4757_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4757_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4757_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4757_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
}
else
{
lean_dec(v_a_4747_);
lean_dec_ref(v_a_4746_);
lean_dec(v_a_4745_);
lean_dec_ref(v_a_4744_);
lean_dec_ref(v_computedFields_4743_);
return v___x_4755_;
}
}
else
{
lean_dec(v_a_4747_);
lean_dec_ref(v_a_4746_);
lean_dec(v_a_4745_);
lean_dec_ref(v_a_4744_);
lean_dec_ref(v_computedFields_4743_);
return v___x_4752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4768_, v_a_4769_, v_a_4770_, v_a_4771_, v_a_4772_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4775_, lean_object* v_as_x27_4776_, lean_object* v_b_4777_, lean_object* v_a_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v___x_4784_; 
v___x_4784_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4776_, v_b_4777_);
return v___x_4784_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4785_, lean_object* v_as_x27_4786_, lean_object* v_b_4787_, lean_object* v_a_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_){
_start:
{
lean_object* v_res_4794_; 
v_res_4794_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4785_, v_as_x27_4786_, v_b_4787_, v_a_4788_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v___y_4790_);
lean_dec_ref(v___y_4789_);
lean_dec(v_as_4785_);
return v_res_4794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4795_, size_t v_sz_4796_, size_t v_i_4797_, lean_object* v_b_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v___x_4804_; 
v___x_4804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4795_, v_sz_4796_, v_i_4797_, v_b_4798_, v___y_4802_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4805_, lean_object* v_sz_4806_, lean_object* v_i_4807_, lean_object* v_b_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
size_t v_sz_boxed_4814_; size_t v_i_boxed_4815_; lean_object* v_res_4816_; 
v_sz_boxed_4814_ = lean_unbox_usize(v_sz_4806_);
lean_dec(v_sz_4806_);
v_i_boxed_4815_ = lean_unbox_usize(v_i_4807_);
lean_dec(v_i_4807_);
v_res_4816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4805_, v_sz_boxed_4814_, v_i_boxed_4815_, v_b_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec_ref(v_as_4805_);
return v_res_4816_;
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
res = l_Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_ComputedFields_computedFieldAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_ComputedFields_computedFieldAttr);
lean_dec_ref(res);
res = l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_ComputedFields_computedFieldAttr___regBuiltin_Lean_Elab_ComputedFields_computedFieldAttr_declRange__3();
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
