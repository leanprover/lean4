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
v___x_658__overap_226_ = lean_panic_fn(v___x_225_, v_msg_195_);
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
v___x_265_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_initFn_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2__spec__0___redArg(v___x_264_, v___y_255_, v___y_256_);
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
lean_object* v___f_402_; lean_object* v___x_3993__overap_403_; lean_object* v___x_404_; 
v___f_402_ = ((lean_object*)(l_panic___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__1___closed__0));
v___x_3993__overap_403_ = lean_panic_fn(v___f_402_, v_msg_396_);
lean_inc(v___y_400_);
lean_inc_ref(v___y_399_);
lean_inc(v___y_398_);
lean_inc_ref(v___y_397_);
v___x_404_ = lean_apply_5(v___x_3993__overap_403_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, lean_box(0));
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
lean_dec_ref(v_ctorTerm_432_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v_e_433_);
return v___x_529_;
}
case 6:
{
lean_object* v___x_530_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v_e_433_);
return v___x_530_;
}
case 7:
{
lean_object* v___x_531_; 
lean_dec_ref(v_ctorTerm_432_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_e_433_);
return v___x_531_;
}
case 9:
{
lean_object* v___x_532_; 
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
lean_dec_ref(v_ctorTerm_432_);
return v___x_535_;
}
else
{
uint8_t v___x_538_; lean_object* v___x_539_; 
lean_dec_ref(v___x_535_);
v___x_538_ = 0;
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
lean_dec_ref(v_ctorTerm_558_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_e_559_);
return v___x_655_;
}
case 6:
{
lean_object* v___x_656_; 
lean_dec_ref(v_ctorTerm_558_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_e_559_);
return v___x_656_;
}
case 7:
{
lean_object* v___x_657_; 
lean_dec_ref(v_ctorTerm_558_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_e_559_);
return v___x_657_;
}
case 9:
{
lean_object* v___x_658_; 
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
lean_dec_ref(v_ctorTerm_558_);
return v___x_661_;
}
else
{
uint8_t v___x_664_; lean_object* v___x_665_; 
lean_dec_ref(v___x_661_);
v___x_664_ = 0;
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
lean_dec(v_a_697_);
lean_dec_ref(v_a_696_);
lean_dec(v_a_695_);
lean_dec_ref(v_a_694_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2___boxed(lean_object* v_ctorTerm_700_, lean_object* v_e_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0_spec__2(v_ctorTerm_700_, v_e_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_);
lean_dec(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec_ref(v_a_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0___boxed(lean_object* v_ctorTerm_708_, lean_object* v_e_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_whnfEasyCases___at___00Lean_Meta_whnfHeadPred___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__0_spec__0(v_ctorTerm_708_, v_e_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_);
lean_dec(v_a_713_);
lean_dec_ref(v_a_712_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
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
v___x_759_ = l_StateRefT_x27_instMonad___redArg(v___x_758_);
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
v___x_783_ = l_StateRefT_x27_instMonad___redArg(v___x_782_);
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
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_3983__overap_809_; lean_object* v___x_810_; 
v___x_807_ = lean_box(0);
v___x_808_ = l_instInhabitedOfMonad___redArg(v___x_806_, v___x_807_);
v___x_3983__overap_809_ = lean_panic_fn(v___x_808_, v_msg_752_);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
v___x_810_ = lean_apply_5(v___x_3983__overap_809_, v___y_753_, v___y_754_, v___y_755_, v___y_756_, lean_box(0));
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
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
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
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2___boxed(lean_object* v_constName_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2(v_constName_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
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
lean_dec_ref(v_ctorTerm_894_);
lean_dec(v_computedField_893_);
return v___x_956_;
}
}
}
else
{
lean_dec(v_ctorName_901_);
lean_dec_ref(v_ctorTerm_894_);
lean_dec(v_computedField_893_);
return v___x_934_;
}
}
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_ctorName_901_);
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
return v___x_918_;
}
}
else
{
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
lean_dec(v_a_979_);
lean_dec_ref(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
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
lean_dec(v_a_1092_);
v_a_1084_ = v___x_1093_;
goto v___jp_1083_;
}
else
{
if (v___x_1102_ == 0)
{
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
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref(v___x_1113_);
v_a_1084_ = v___x_1093_;
goto v___jp_1083_;
}
else
{
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
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
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
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
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
lean_inc(v___y_1200_);
lean_inc_ref(v___y_1199_);
lean_inc(v___y_1198_);
lean_inc_ref(v___y_1197_);
lean_inc_ref(v___y_1194_);
v___x_1202_ = lean_apply_8(v_k_1193_, v_b_1195_, v_c_1196_, v___y_1194_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, lean_box(0));
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0___boxed(lean_object* v_k_1203_, lean_object* v___y_1204_, lean_object* v_b_1205_, lean_object* v_c_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg___lam__0(v_k_1203_, v___y_1204_, v_b_1205_, v_c_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec_ref(v___y_1204_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(lean_object* v_type_1213_, lean_object* v_k_1214_, uint8_t v_cleanupAnnotations_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v___f_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_inc_ref(v___y_1216_);
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
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec_ref(v___y_1237_);
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
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec_ref(v___y_1260_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0(lean_object* v_head_1273_, lean_object* v_name_1274_, lean_object* v_lparams_1275_, lean_object* v_params_1276_, lean_object* v_compFieldVars_1277_, lean_object* v_fields_1278_, lean_object* v_retTy_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
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
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
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
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
lean_dec(v___y_1404_);
lean_dec_ref(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType(lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_){
_start:
{
lean_object* v_toInductiveVal_1415_; lean_object* v_toConstantVal_1416_; lean_object* v_lparams_1417_; lean_object* v_params_1418_; lean_object* v_compFieldVars_1419_; lean_object* v_numParams_1420_; lean_object* v_ctors_1421_; uint8_t v_isUnsafe_1422_; lean_object* v_name_1423_; lean_object* v_levelParams_1424_; lean_object* v_type_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_toInductiveVal_1415_ = lean_ctor_get(v_a_1409_, 0);
v_toConstantVal_1416_ = lean_ctor_get(v_toInductiveVal_1415_, 0);
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
lean_inc(v_name_1423_);
v_levelParams_1424_ = lean_ctor_get(v_toConstantVal_1416_, 1);
lean_inc(v_levelParams_1424_);
v_type_1425_ = lean_ctor_get(v_toConstantVal_1416_, 2);
lean_inc_ref(v_type_1425_);
v___x_1426_ = lean_box(0);
lean_inc(v_name_1423_);
v___x_1427_ = l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1(v_name_1423_, v_lparams_1417_, v_params_1418_, v_compFieldVars_1419_, v_ctors_1421_, v___x_1426_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_);
lean_dec_ref(v_a_1409_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v___x_1429_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
v___x_1430_ = l_Lean_Name_append(v_name_1423_, v___x_1429_);
v___x_1431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v_type_1425_);
lean_ctor_set(v___x_1431_, 2, v_a_1428_);
v___x_1432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
lean_ctor_set(v___x_1432_, 1, v___x_1426_);
v___x_1433_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_1433_, 0, v_levelParams_1424_);
lean_ctor_set(v___x_1433_, 1, v_numParams_1420_);
lean_ctor_set(v___x_1433_, 2, v___x_1432_);
lean_ctor_set_uint8(v___x_1433_, sizeof(void*)*3, v_isUnsafe_1422_);
v___x_1434_ = 0;
v___x_1435_ = l_Lean_addDecl(v___x_1433_, v___x_1434_, v_a_1412_, v_a_1413_);
return v___x_1435_;
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref(v_type_1425_);
lean_dec(v_levelParams_1424_);
lean_dec(v_name_1423_);
lean_dec(v_numParams_1420_);
v_a_1436_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1427_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1427_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkImplType___boxed(lean_object* v_a_1444_, lean_object* v_a_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_Elab_ComputedFields_mkImplType(v_a_1444_, v_a_1445_, v_a_1446_, v_a_1447_, v_a_1448_);
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(lean_object* v_k_1451_, lean_object* v___y_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc(v___y_1455_);
lean_inc_ref(v___y_1454_);
lean_inc_ref(v___y_1452_);
v___x_1459_ = lean_apply_7(v_k_1451_, v_b_1453_, v___y_1452_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, lean_box(0));
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed(lean_object* v_k_1460_, lean_object* v___y_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0(v_k_1460_, v___y_1461_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec_ref(v___y_1461_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(lean_object* v_name_1469_, lean_object* v_type_1470_, lean_object* v_val_1471_, lean_object* v_k_1472_, uint8_t v_nondep_1473_, uint8_t v_kind_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___f_1481_; lean_object* v___x_1482_; 
lean_inc_ref(v___y_1475_);
v___f_1481_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1481_, 0, v_k_1472_);
lean_closure_set(v___f_1481_, 1, v___y_1475_);
v___x_1482_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_1469_, v_type_1470_, v_val_1471_, v___f_1481_, v_nondep_1473_, v_kind_1474_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1482_) == 0)
{
return v___x_1482_;
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1482_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1482_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___boxed(lean_object* v_name_1491_, lean_object* v_type_1492_, lean_object* v_val_1493_, lean_object* v_k_1494_, lean_object* v_nondep_1495_, lean_object* v_kind_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_nondep_boxed_1503_; uint8_t v_kind_boxed_1504_; lean_object* v_res_1505_; 
v_nondep_boxed_1503_ = lean_unbox(v_nondep_1495_);
v_kind_boxed_1504_ = lean_unbox(v_kind_1496_);
v_res_1505_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1491_, v_type_1492_, v_val_1493_, v_k_1494_, v_nondep_boxed_1503_, v_kind_boxed_1504_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec_ref(v___y_1497_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(lean_object* v_00_u03b1_1506_, lean_object* v_name_1507_, lean_object* v_type_1508_, lean_object* v_val_1509_, lean_object* v_k_1510_, uint8_t v_nondep_1511_, uint8_t v_kind_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v_name_1507_, v_type_1508_, v_val_1509_, v_k_1510_, v_nondep_1511_, v_kind_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___boxed(lean_object* v_00_u03b1_1520_, lean_object* v_name_1521_, lean_object* v_type_1522_, lean_object* v_val_1523_, lean_object* v_k_1524_, lean_object* v_nondep_1525_, lean_object* v_kind_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
uint8_t v_nondep_boxed_1533_; uint8_t v_kind_boxed_1534_; lean_object* v_res_1535_; 
v_nondep_boxed_1533_ = lean_unbox(v_nondep_1525_);
v_kind_boxed_1534_ = lean_unbox(v_kind_1526_);
v_res_1535_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2(v_00_u03b1_1520_, v_name_1521_, v_type_1522_, v_val_1523_, v_k_1524_, v_nondep_boxed_1533_, v_kind_boxed_1534_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(lean_object* v___x_1536_, lean_object* v___x_1537_, lean_object* v_majorImpl_1538_, lean_object* v_m_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; uint8_t v___x_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v___x_1546_ = lean_mk_empty_array_with_capacity(v___x_1536_);
lean_inc_ref(v_m_1539_);
lean_inc_ref(v___x_1546_);
v___x_1547_ = lean_array_push(v___x_1546_, v_m_1539_);
v___x_1548_ = l_Array_append___redArg(v___x_1547_, v___x_1537_);
v___x_1549_ = lean_array_push(v___x_1546_, v_majorImpl_1538_);
v___x_1550_ = l_Array_append___redArg(v___x_1548_, v___x_1549_);
lean_dec_ref(v___x_1549_);
v___x_1551_ = 0;
v___x_1552_ = 1;
v___x_1553_ = 1;
v___x_1554_ = l_Lean_Meta_mkLambdaFVars(v___x_1550_, v_m_1539_, v___x_1551_, v___x_1552_, v___x_1551_, v___x_1552_, v___x_1553_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec_ref(v___x_1550_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed(lean_object* v___x_1555_, lean_object* v___x_1556_, lean_object* v_majorImpl_1557_, lean_object* v_m_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0(v___x_1555_, v___x_1556_, v_majorImpl_1557_, v_m_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec_ref(v___x_1556_);
lean_dec(v___x_1555_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(lean_object* v_constMotive_1569_, lean_object* v___x_1570_, lean_object* v___x_1571_, lean_object* v_majorImpl_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
lean_inc(v___y_1577_);
lean_inc_ref(v___y_1576_);
lean_inc(v___y_1575_);
lean_inc_ref(v___y_1574_);
lean_inc_ref(v_constMotive_1569_);
v___x_1579_ = lean_infer_type(v_constMotive_1569_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v_a_1580_; lean_object* v___f_1581_; lean_object* v___x_1582_; uint8_t v___x_1583_; uint8_t v___x_1584_; lean_object* v___x_1585_; 
v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_a_1580_);
lean_dec_ref(v___x_1579_);
v___f_1581_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__0___boxed), 10, 3);
lean_closure_set(v___f_1581_, 0, v___x_1570_);
lean_closure_set(v___f_1581_, 1, v___x_1571_);
lean_closure_set(v___f_1581_, 2, v_majorImpl_1572_);
v___x_1582_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___closed__1));
v___x_1583_ = 0;
v___x_1584_ = 0;
v___x_1585_ = l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg(v___x_1582_, v_a_1580_, v_constMotive_1569_, v___f_1581_, v___x_1583_, v___x_1584_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
return v___x_1585_;
}
else
{
lean_dec_ref(v_majorImpl_1572_);
lean_dec_ref(v___x_1571_);
lean_dec(v___x_1570_);
lean_dec_ref(v_constMotive_1569_);
return v___x_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed(lean_object* v_constMotive_1586_, lean_object* v___x_1587_, lean_object* v___x_1588_, lean_object* v_majorImpl_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1(v_constMotive_1586_, v___x_1587_, v___x_1588_, v_majorImpl_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec_ref(v___y_1590_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(lean_object* v_name_1597_, uint8_t v_bi_1598_, lean_object* v_type_1599_, lean_object* v_k_1600_, uint8_t v_kind_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v___f_1608_; lean_object* v___x_1609_; 
lean_inc_ref(v___y_1602_);
v___f_1608_ = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__2___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_1608_, 0, v_k_1600_);
lean_closure_set(v___f_1608_, 1, v___y_1602_);
v___x_1609_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1597_, v_bi_1598_, v_type_1599_, v___f_1608_, v_kind_1601_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
if (lean_obj_tag(v___x_1609_) == 0)
{
return v___x_1609_;
}
else
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1617_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1617_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1615_; 
if (v_isShared_1613_ == 0)
{
v___x_1615_ = v___x_1612_;
goto v_reusejp_1614_;
}
else
{
lean_object* v_reuseFailAlloc_1616_; 
v_reuseFailAlloc_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1616_, 0, v_a_1610_);
v___x_1615_ = v_reuseFailAlloc_1616_;
goto v_reusejp_1614_;
}
v_reusejp_1614_:
{
return v___x_1615_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg___boxed(lean_object* v_name_1618_, lean_object* v_bi_1619_, lean_object* v_type_1620_, lean_object* v_k_1621_, lean_object* v_kind_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
uint8_t v_bi_boxed_1629_; uint8_t v_kind_boxed_1630_; lean_object* v_res_1631_; 
v_bi_boxed_1629_ = lean_unbox(v_bi_1619_);
v_kind_boxed_1630_ = lean_unbox(v_kind_1622_);
v_res_1631_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1618_, v_bi_boxed_1629_, v_type_1620_, v_k_1621_, v_kind_boxed_1630_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec_ref(v___y_1623_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(lean_object* v_name_1632_, lean_object* v_type_1633_, lean_object* v_k_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
uint8_t v___x_1641_; uint8_t v___x_1642_; lean_object* v___x_1643_; 
v___x_1641_ = 0;
v___x_1642_ = 0;
v___x_1643_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_1632_, v___x_1641_, v_type_1633_, v_k_1634_, v___x_1642_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg___boxed(lean_object* v_name_1644_, lean_object* v_type_1645_, lean_object* v_k_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_1644_, v_type_1645_, v_k_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_, v___y_1651_);
lean_dec(v___y_1651_);
lean_dec_ref(v___y_1650_);
lean_dec(v___y_1649_);
lean_dec_ref(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
if (lean_obj_tag(v_a_1654_) == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = l_List_reverse___redArg(v_a_1655_);
return v___x_1656_;
}
else
{
lean_object* v_head_1657_; lean_object* v_tail_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1667_; 
v_head_1657_ = lean_ctor_get(v_a_1654_, 0);
v_tail_1658_ = lean_ctor_get(v_a_1654_, 1);
v_isSharedCheck_1667_ = !lean_is_exclusive(v_a_1654_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1660_ = v_a_1654_;
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
else
{
lean_inc(v_tail_1658_);
lean_inc(v_head_1657_);
lean_dec(v_a_1654_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1667_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = l_Lean_mkLevelParam(v_head_1657_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 1, v_a_1655_);
lean_ctor_set(v___x_1660_, 0, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1666_, 1, v_a_1655_);
v___x_1664_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
v_a_1654_ = v_tail_1658_;
v_a_1655_ = v___x_1664_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(lean_object* v_a_1668_, lean_object* v_b_1669_){
_start:
{
lean_object* v_array_1670_; lean_object* v_start_1671_; lean_object* v_stop_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1685_; 
v_array_1670_ = lean_ctor_get(v_a_1668_, 0);
v_start_1671_ = lean_ctor_get(v_a_1668_, 1);
v_stop_1672_ = lean_ctor_get(v_a_1668_, 2);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_a_1668_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1674_ = v_a_1668_;
v_isShared_1675_ = v_isSharedCheck_1685_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_stop_1672_);
lean_inc(v_start_1671_);
lean_inc(v_array_1670_);
lean_dec(v_a_1668_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1685_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_nat_dec_lt(v_start_1671_, v_stop_1672_);
if (v___x_1676_ == 0)
{
lean_del_object(v___x_1674_);
lean_dec(v_stop_1672_);
lean_dec(v_start_1671_);
lean_dec_ref(v_array_1670_);
return v_b_1669_;
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1677_ = lean_unsigned_to_nat(1u);
v___x_1678_ = lean_nat_add(v_start_1671_, v___x_1677_);
lean_inc_ref(v_array_1670_);
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 1, v___x_1678_);
v___x_1680_ = v___x_1674_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_array_1670_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_stop_1672_);
v___x_1680_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_array_fget(v_array_1670_, v_start_1671_);
lean_dec(v_start_1671_);
lean_dec_ref(v_array_1670_);
v___x_1682_ = lean_array_push(v_b_1669_, v___x_1681_);
v_a_1668_ = v___x_1680_;
v_b_1669_ = v___x_1682_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(lean_object* v_b_1686_, lean_object* v_a_1687_, lean_object* v_constMotive_1688_, uint8_t v___x_1689_, lean_object* v_compFieldVars_1690_, lean_object* v_args_1691_, lean_object* v_x_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Elab_ComputedFields_isScalarField(v_b_1686_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = l_Lean_mkAppN(v_a_1687_, v_args_1691_);
v___x_1702_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_constMotive_1688_, v___x_1701_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___y_1705_; uint8_t v___x_1710_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1702_);
v___x_1710_ = lean_unbox(v_a_1700_);
lean_dec(v_a_1700_);
if (v___x_1710_ == 0)
{
v___y_1705_ = v_compFieldVars_1690_;
goto v___jp_1704_;
}
else
{
lean_object* v___x_1711_; 
lean_dec_ref(v_compFieldVars_1690_);
v___x_1711_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___y_1705_ = v___x_1711_;
goto v___jp_1704_;
}
v___jp_1704_:
{
lean_object* v___x_1706_; uint8_t v___x_1707_; uint8_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1706_ = l_Array_append___redArg(v___y_1705_, v_args_1691_);
v___x_1707_ = 0;
v___x_1708_ = 1;
v___x_1709_ = l_Lean_Meta_mkLambdaFVars(v___x_1706_, v_a_1703_, v___x_1707_, v___x_1689_, v___x_1707_, v___x_1689_, v___x_1708_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
lean_dec_ref(v___x_1706_);
return v___x_1709_;
}
}
else
{
lean_dec(v_a_1700_);
lean_dec_ref(v_compFieldVars_1690_);
return v___x_1702_;
}
}
else
{
lean_object* v_a_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1719_; 
lean_dec_ref(v_compFieldVars_1690_);
lean_dec_ref(v_constMotive_1688_);
lean_dec_ref(v_a_1687_);
v_a_1712_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1714_ = v___x_1699_;
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_a_1712_);
lean_dec(v___x_1699_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1719_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1717_; 
if (v_isShared_1715_ == 0)
{
v___x_1717_ = v___x_1714_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed(lean_object* v_b_1720_, lean_object* v_a_1721_, lean_object* v_constMotive_1722_, lean_object* v___x_1723_, lean_object* v_compFieldVars_1724_, lean_object* v_args_1725_, lean_object* v_x_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_12673__boxed_1733_; lean_object* v_res_1734_; 
v___x_12673__boxed_1733_ = lean_unbox(v___x_1723_);
v_res_1734_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0(v_b_1720_, v_a_1721_, v_constMotive_1722_, v___x_12673__boxed_1733_, v_compFieldVars_1724_, v_args_1725_, v_x_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec_ref(v_x_1726_);
lean_dec_ref(v_args_1725_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(lean_object* v_constMotive_1735_, lean_object* v_compFieldVars_1736_, lean_object* v_as_1737_, lean_object* v_bs_1738_, lean_object* v_i_1739_, lean_object* v_cs_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v___y_1748_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v___x_1762_ = lean_array_get_size(v_as_1737_);
v___x_1763_ = lean_nat_dec_lt(v_i_1739_, v___x_1762_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_dec(v_i_1739_);
lean_dec_ref(v_compFieldVars_1736_);
lean_dec_ref(v_constMotive_1735_);
v___x_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1764_, 0, v_cs_1740_);
return v___x_1764_;
}
else
{
lean_object* v___x_1765_; uint8_t v___x_1766_; 
v___x_1765_ = lean_array_get_size(v_bs_1738_);
v___x_1766_ = lean_nat_dec_lt(v_i_1739_, v___x_1765_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
lean_dec(v_i_1739_);
lean_dec_ref(v_compFieldVars_1736_);
lean_dec_ref(v_constMotive_1735_);
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_cs_1740_);
return v___x_1767_;
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1769_; 
v_a_1768_ = lean_array_fget_borrowed(v_as_1737_, v_i_1739_);
lean_inc(v___y_1745_);
lean_inc_ref(v___y_1744_);
lean_inc(v___y_1743_);
lean_inc_ref(v___y_1742_);
lean_inc(v_a_1768_);
v___x_1769_ = lean_infer_type(v_a_1768_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v_b_1771_; lean_object* v___x_1772_; lean_object* v___f_1773_; uint8_t v___x_1774_; lean_object* v___x_1775_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref(v___x_1769_);
v_b_1771_ = lean_array_fget_borrowed(v_bs_1738_, v_i_1739_);
v___x_1772_ = lean_box(v___x_1766_);
lean_inc_ref(v_compFieldVars_1736_);
lean_inc_ref(v_constMotive_1735_);
lean_inc(v_a_1768_);
lean_inc(v_b_1771_);
v___f_1773_ = lean_alloc_closure((void*)(l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___lam__0___boxed), 13, 5);
lean_closure_set(v___f_1773_, 0, v_b_1771_);
lean_closure_set(v___f_1773_, 1, v_a_1768_);
lean_closure_set(v___f_1773_, 2, v_constMotive_1735_);
lean_closure_set(v___f_1773_, 3, v___x_1772_);
lean_closure_set(v___f_1773_, 4, v_compFieldVars_1736_);
v___x_1774_ = 0;
v___x_1775_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_1770_, v___f_1773_, v___x_1774_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
v___y_1748_ = v___x_1775_;
goto v___jp_1747_;
}
else
{
v___y_1748_ = v___x_1769_;
goto v___jp_1747_;
}
}
}
v___jp_1747_:
{
if (lean_obj_tag(v___y_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v_a_1749_ = lean_ctor_get(v___y_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___y_1748_);
v___x_1750_ = lean_unsigned_to_nat(1u);
v___x_1751_ = lean_nat_add(v_i_1739_, v___x_1750_);
lean_dec(v_i_1739_);
v___x_1752_ = lean_array_push(v_cs_1740_, v_a_1749_);
v_i_1739_ = v___x_1751_;
v_cs_1740_ = v___x_1752_;
goto _start;
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
lean_dec_ref(v_cs_1740_);
lean_dec(v_i_1739_);
lean_dec_ref(v_compFieldVars_1736_);
lean_dec_ref(v_constMotive_1735_);
v_a_1754_ = lean_ctor_get(v___y_1748_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___y_1748_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___y_1748_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___y_1748_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4___boxed(lean_object* v_constMotive_1776_, lean_object* v_compFieldVars_1777_, lean_object* v_as_1778_, lean_object* v_bs_1779_, lean_object* v_i_1780_, lean_object* v_cs_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1776_, v_compFieldVars_1777_, v_as_1778_, v_bs_1779_, v_i_1780_, v_cs_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec_ref(v_bs_1779_);
lean_dec_ref(v_as_1778_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(lean_object* v_numIndices_1792_, lean_object* v___x_1793_, lean_object* v___x_1794_, lean_object* v_lparams_1795_, lean_object* v_params_1796_, lean_object* v_ctors_1797_, lean_object* v_compFieldVars_1798_, lean_object* v_levelParams_1799_, lean_object* v_xs_1800_, lean_object* v_constMotive_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___y_1817_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v___x_1808_ = lean_unsigned_to_nat(1u);
v___x_1809_ = lean_nat_add(v_numIndices_1792_, v___x_1808_);
lean_inc(v___x_1809_);
lean_inc_ref(v_xs_1800_);
v___x_1810_ = l_Array_toSubarray___redArg(v_xs_1800_, v___x_1808_, v___x_1809_);
v___x_1811_ = lean_unsigned_to_nat(0u);
v___x_1812_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_1813_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1810_, v___x_1812_);
lean_inc_ref(v___x_1813_);
lean_inc_ref(v_constMotive_1801_);
v___f_1814_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__1___boxed), 10, 3);
lean_closure_set(v___f_1814_, 0, v_constMotive_1801_);
lean_closure_set(v___f_1814_, 1, v___x_1808_);
lean_closure_set(v___f_1814_, 2, v___x_1813_);
v___x_1815_ = lean_array_get_borrowed(v___x_1793_, v_xs_1800_, v___x_1809_);
lean_dec(v___x_1809_);
v___x_1858_ = lean_unsigned_to_nat(2u);
v___x_1859_ = lean_nat_add(v_numIndices_1792_, v___x_1858_);
v___x_1860_ = lean_array_get_size(v_xs_1800_);
v___x_1861_ = lean_nat_dec_le(v___x_1859_, v___x_1811_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1859_);
lean_ctor_set(v___x_1862_, 1, v___x_1860_);
v___y_1817_ = v___x_1862_;
goto v___jp_1816_;
}
else
{
lean_object* v___x_1863_; 
lean_dec(v___x_1859_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1811_);
lean_ctor_set(v___x_1863_, 1, v___x_1860_);
v___y_1817_ = v___x_1863_;
goto v___jp_1816_;
}
v___jp_1816_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_inc(v___x_1794_);
v___x_1818_ = l_Lean_mkConst(v___x_1794_, v_lparams_1795_);
lean_inc_ref(v_params_1796_);
v___x_1819_ = l_Array_append___redArg(v_params_1796_, v___x_1813_);
v___x_1820_ = l_Lean_mkAppN(v___x_1818_, v___x_1819_);
lean_dec_ref(v___x_1819_);
v___x_1821_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___closed__1));
lean_inc_ref(v___x_1820_);
v___x_1822_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_1821_, v___x_1820_, v___f_1814_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
if (lean_obj_tag(v___x_1822_) == 0)
{
lean_object* v_a_1823_; lean_object* v___x_1824_; 
v_a_1823_ = lean_ctor_get(v___x_1822_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1822_);
lean_inc(v___x_1815_);
v___x_1824_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v___x_1820_, v___x_1815_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v_lower_1826_; lean_object* v_upper_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1825_);
lean_dec_ref(v___x_1824_);
v_lower_1826_ = lean_ctor_get(v___y_1817_, 0);
lean_inc(v_lower_1826_);
v_upper_1827_ = lean_ctor_get(v___y_1817_, 1);
lean_inc(v_upper_1827_);
lean_dec_ref(v___y_1817_);
lean_inc_ref(v_xs_1800_);
v___x_1828_ = l_Array_toSubarray___redArg(v_xs_1800_, v_lower_1826_, v_upper_1827_);
v___x_1829_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_1828_, v___x_1812_);
v___x_1830_ = lean_array_mk(v_ctors_1797_);
v___x_1831_ = l_Array_zipWithMAux___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__4(v_constMotive_1801_, v_compFieldVars_1798_, v___x_1829_, v___x_1830_, v___x_1811_, v___x_1812_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec_ref(v___x_1830_);
lean_dec_ref(v___x_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_a_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; uint8_t v___x_1846_; uint8_t v___x_1847_; uint8_t v___x_1848_; lean_object* v___x_1849_; 
v_a_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___x_1831_);
lean_inc_ref(v_params_1796_);
v___x_1833_ = l_Array_append___redArg(v_params_1796_, v_xs_1800_);
lean_dec_ref(v_xs_1800_);
v___x_1834_ = l_Lean_mkCasesOnName(v___x_1794_);
v___x_1835_ = lean_box(0);
v___x_1836_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_1799_, v___x_1835_);
v___x_1837_ = l_Lean_mkConst(v___x_1834_, v___x_1836_);
v___x_1838_ = lean_mk_empty_array_with_capacity(v___x_1808_);
lean_inc_ref(v___x_1838_);
v___x_1839_ = lean_array_push(v___x_1838_, v_a_1823_);
v___x_1840_ = l_Array_append___redArg(v_params_1796_, v___x_1839_);
lean_dec_ref(v___x_1839_);
v___x_1841_ = l_Array_append___redArg(v___x_1840_, v___x_1813_);
lean_dec_ref(v___x_1813_);
v___x_1842_ = lean_array_push(v___x_1838_, v_a_1825_);
v___x_1843_ = l_Array_append___redArg(v___x_1841_, v___x_1842_);
lean_dec_ref(v___x_1842_);
v___x_1844_ = l_Array_append___redArg(v___x_1843_, v_a_1832_);
lean_dec(v_a_1832_);
v___x_1845_ = l_Lean_mkAppN(v___x_1837_, v___x_1844_);
lean_dec_ref(v___x_1844_);
v___x_1846_ = 0;
v___x_1847_ = 1;
v___x_1848_ = 1;
v___x_1849_ = l_Lean_Meta_mkLambdaFVars(v___x_1833_, v___x_1845_, v___x_1846_, v___x_1847_, v___x_1846_, v___x_1847_, v___x_1848_, v___y_1803_, v___y_1804_, v___y_1805_, v___y_1806_);
lean_dec_ref(v___x_1833_);
return v___x_1849_;
}
else
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1857_; 
lean_dec(v_a_1825_);
lean_dec(v_a_1823_);
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_xs_1800_);
lean_dec(v_levelParams_1799_);
lean_dec_ref(v_params_1796_);
lean_dec(v___x_1794_);
v_a_1850_ = lean_ctor_get(v___x_1831_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1831_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1852_ = v___x_1831_;
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1831_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1857_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1855_; 
if (v_isShared_1853_ == 0)
{
v___x_1855_ = v___x_1852_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_a_1850_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
else
{
lean_dec(v_a_1823_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_constMotive_1801_);
lean_dec_ref(v_xs_1800_);
lean_dec(v_levelParams_1799_);
lean_dec_ref(v_compFieldVars_1798_);
lean_dec(v_ctors_1797_);
lean_dec_ref(v_params_1796_);
lean_dec(v___x_1794_);
return v___x_1824_;
}
}
else
{
lean_dec_ref(v___x_1820_);
lean_dec_ref(v___y_1817_);
lean_dec_ref(v___x_1813_);
lean_dec_ref(v_constMotive_1801_);
lean_dec_ref(v_xs_1800_);
lean_dec(v_levelParams_1799_);
lean_dec_ref(v_compFieldVars_1798_);
lean_dec(v_ctors_1797_);
lean_dec_ref(v_params_1796_);
lean_dec(v___x_1794_);
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed(lean_object* v_numIndices_1864_, lean_object* v___x_1865_, lean_object* v___x_1866_, lean_object* v_lparams_1867_, lean_object* v_params_1868_, lean_object* v_ctors_1869_, lean_object* v_compFieldVars_1870_, lean_object* v_levelParams_1871_, lean_object* v_xs_1872_, lean_object* v_constMotive_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_, lean_object* v___y_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2(v_numIndices_1864_, v___x_1865_, v___x_1866_, v_lparams_1867_, v_params_1868_, v_ctors_1869_, v_compFieldVars_1870_, v_levelParams_1871_, v_xs_1872_, v_constMotive_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec(v___y_1878_);
lean_dec_ref(v___y_1877_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
lean_dec_ref(v___y_1874_);
lean_dec(v_numIndices_1864_);
return v_res_1880_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1881_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; 
v___x_1882_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__0);
v___x_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
return v___x_1883_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v___x_1884_);
return v___x_1885_;
}
}
static lean_object* _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__1);
v___x_1887_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1887_, 0, v___x_1886_);
lean_ctor_set(v___x_1887_, 1, v___x_1886_);
lean_ctor_set(v___x_1887_, 2, v___x_1886_);
lean_ctor_set(v___x_1887_, 3, v___x_1886_);
lean_ctor_set(v___x_1887_, 4, v___x_1886_);
lean_ctor_set(v___x_1887_, 5, v___x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(lean_object* v_env_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v___x_1892_; lean_object* v_nextMacroScope_1893_; lean_object* v_ngen_1894_; lean_object* v_auxDeclNGen_1895_; lean_object* v_traceState_1896_; lean_object* v_messages_1897_; lean_object* v_infoState_1898_; lean_object* v_snapshotTasks_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1925_; 
v___x_1892_ = lean_st_ref_take(v___y_1890_);
v_nextMacroScope_1893_ = lean_ctor_get(v___x_1892_, 1);
v_ngen_1894_ = lean_ctor_get(v___x_1892_, 2);
v_auxDeclNGen_1895_ = lean_ctor_get(v___x_1892_, 3);
v_traceState_1896_ = lean_ctor_get(v___x_1892_, 4);
v_messages_1897_ = lean_ctor_get(v___x_1892_, 6);
v_infoState_1898_ = lean_ctor_get(v___x_1892_, 7);
v_snapshotTasks_1899_ = lean_ctor_get(v___x_1892_, 8);
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1892_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; lean_object* v_unused_1927_; 
v_unused_1926_ = lean_ctor_get(v___x_1892_, 5);
lean_dec(v_unused_1926_);
v_unused_1927_ = lean_ctor_get(v___x_1892_, 0);
lean_dec(v_unused_1927_);
v___x_1901_ = v___x_1892_;
v_isShared_1902_ = v_isSharedCheck_1925_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_snapshotTasks_1899_);
lean_inc(v_infoState_1898_);
lean_inc(v_messages_1897_);
lean_inc(v_traceState_1896_);
lean_inc(v_auxDeclNGen_1895_);
lean_inc(v_ngen_1894_);
lean_inc(v_nextMacroScope_1893_);
lean_dec(v___x_1892_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1925_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1905_; 
v___x_1903_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 5, v___x_1903_);
lean_ctor_set(v___x_1901_, 0, v_env_1888_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_env_1888_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_nextMacroScope_1893_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_ngen_1894_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_auxDeclNGen_1895_);
lean_ctor_set(v_reuseFailAlloc_1924_, 4, v_traceState_1896_);
lean_ctor_set(v_reuseFailAlloc_1924_, 5, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1924_, 6, v_messages_1897_);
lean_ctor_set(v_reuseFailAlloc_1924_, 7, v_infoState_1898_);
lean_ctor_set(v_reuseFailAlloc_1924_, 8, v_snapshotTasks_1899_);
v___x_1905_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v_mctx_1908_; lean_object* v_zetaDeltaFVarIds_1909_; lean_object* v_postponed_1910_; lean_object* v_diag_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1922_; 
v___x_1906_ = lean_st_ref_set(v___y_1890_, v___x_1905_);
v___x_1907_ = lean_st_ref_take(v___y_1889_);
v_mctx_1908_ = lean_ctor_get(v___x_1907_, 0);
v_zetaDeltaFVarIds_1909_ = lean_ctor_get(v___x_1907_, 2);
v_postponed_1910_ = lean_ctor_get(v___x_1907_, 3);
v_diag_1911_ = lean_ctor_get(v___x_1907_, 4);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1922_ == 0)
{
lean_object* v_unused_1923_; 
v_unused_1923_ = lean_ctor_get(v___x_1907_, 1);
lean_dec(v_unused_1923_);
v___x_1913_ = v___x_1907_;
v_isShared_1914_ = v_isSharedCheck_1922_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_diag_1911_);
lean_inc(v_postponed_1910_);
lean_inc(v_zetaDeltaFVarIds_1909_);
lean_inc(v_mctx_1908_);
lean_dec(v___x_1907_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1922_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1915_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v___x_1915_);
v___x_1917_ = v___x_1913_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_mctx_1908_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1921_, 2, v_zetaDeltaFVarIds_1909_);
lean_ctor_set(v_reuseFailAlloc_1921_, 3, v_postponed_1910_);
lean_ctor_set(v_reuseFailAlloc_1921_, 4, v_diag_1911_);
v___x_1917_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1918_ = lean_st_ref_set(v___y_1889_, v___x_1917_);
v___x_1919_ = lean_box(0);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___boxed(lean_object* v_env_1928_, lean_object* v___y_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
lean_object* v_res_1932_; 
v_res_1932_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_1928_, v___y_1929_, v___y_1930_);
lean_dec(v___y_1930_);
lean_dec(v___y_1929_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(lean_object* v_declName_1933_, lean_object* v_impName_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v___x_1941_; lean_object* v_env_1942_; lean_object* v___x_1943_; 
v___x_1941_ = lean_st_ref_get(v___y_1939_);
v_env_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc_ref(v_env_1942_);
lean_dec(v___x_1941_);
v___x_1943_ = l_Lean_Compiler_setImplementedBy(v_env_1942_, v_declName_1933_, v_impName_1934_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1953_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1946_ = v___x_1943_;
v_isShared_1947_ = v_isSharedCheck_1953_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1953_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
lean_ctor_set_tag(v___x_1946_, 3);
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1950_ = l_Lean_MessageData_ofFormat(v___x_1949_);
v___x_1951_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_1950_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
return v___x_1951_;
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1955_; 
v_a_1954_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1954_);
lean_dec_ref(v___x_1943_);
v___x_1955_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_a_1954_, v___y_1937_, v___y_1939_);
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6___boxed(lean_object* v_declName_1956_, lean_object* v_impName_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_res_1964_; 
v_res_1964_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_declName_1956_, v_impName_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
lean_dec(v___y_1962_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec_ref(v___y_1958_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(lean_object* v_msg_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_toApplicative_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2036_; 
v___x_1972_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__0);
v___x_1973_ = l_StateRefT_x27_instMonad___redArg(v___x_1972_);
v_toApplicative_1974_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v___x_1973_, 1);
lean_dec(v_unused_2037_);
v___x_1976_ = v___x_1973_;
v_isShared_1977_ = v_isSharedCheck_2036_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_toApplicative_1974_);
lean_dec(v___x_1973_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2036_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v_toFunctor_1978_; lean_object* v_toSeq_1979_; lean_object* v_toSeqLeft_1980_; lean_object* v_toSeqRight_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2034_; 
v_toFunctor_1978_ = lean_ctor_get(v_toApplicative_1974_, 0);
v_toSeq_1979_ = lean_ctor_get(v_toApplicative_1974_, 2);
v_toSeqLeft_1980_ = lean_ctor_get(v_toApplicative_1974_, 3);
v_toSeqRight_1981_ = lean_ctor_get(v_toApplicative_1974_, 4);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_toApplicative_1974_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_toApplicative_1974_, 1);
lean_dec(v_unused_2035_);
v___x_1983_ = v_toApplicative_1974_;
v_isShared_1984_ = v_isSharedCheck_2034_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_toSeqRight_1981_);
lean_inc(v_toSeqLeft_1980_);
lean_inc(v_toSeq_1979_);
lean_inc(v_toFunctor_1978_);
lean_dec(v_toApplicative_1974_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2034_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___f_1985_; lean_object* v___f_1986_; lean_object* v___f_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; lean_object* v___f_1990_; lean_object* v___f_1991_; lean_object* v___f_1992_; lean_object* v___x_1994_; 
v___f_1985_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__1));
v___f_1986_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0_spec__0___closed__2));
lean_inc_ref(v_toFunctor_1978_);
v___f_1987_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1987_, 0, v_toFunctor_1978_);
v___f_1988_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1988_, 0, v_toFunctor_1978_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___f_1987_);
lean_ctor_set(v___x_1989_, 1, v___f_1988_);
v___f_1990_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1990_, 0, v_toSeqRight_1981_);
v___f_1991_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1991_, 0, v_toSeqLeft_1980_);
v___f_1992_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1992_, 0, v_toSeq_1979_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 4, v___f_1990_);
lean_ctor_set(v___x_1983_, 3, v___f_1991_);
lean_ctor_set(v___x_1983_, 2, v___f_1992_);
lean_ctor_set(v___x_1983_, 1, v___f_1985_);
lean_ctor_set(v___x_1983_, 0, v___x_1989_);
v___x_1994_ = v___x_1983_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_2033_, 1, v___f_1985_);
lean_ctor_set(v_reuseFailAlloc_2033_, 2, v___f_1992_);
lean_ctor_set(v_reuseFailAlloc_2033_, 3, v___f_1991_);
lean_ctor_set(v_reuseFailAlloc_2033_, 4, v___f_1990_);
v___x_1994_ = v_reuseFailAlloc_2033_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1996_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v___f_1986_);
lean_ctor_set(v___x_1976_, 0, v___x_1994_);
v___x_1996_ = v___x_1976_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_2032_; 
v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2032_, 0, v___x_1994_);
lean_ctor_set(v_reuseFailAlloc_2032_, 1, v___f_1986_);
v___x_1996_ = v_reuseFailAlloc_2032_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
lean_object* v___x_1997_; lean_object* v_toApplicative_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2030_; 
v___x_1997_ = l_StateRefT_x27_instMonad___redArg(v___x_1996_);
v_toApplicative_1998_ = lean_ctor_get(v___x_1997_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1997_);
if (v_isSharedCheck_2030_ == 0)
{
lean_object* v_unused_2031_; 
v_unused_2031_ = lean_ctor_get(v___x_1997_, 1);
lean_dec(v_unused_2031_);
v___x_2000_ = v___x_1997_;
v_isShared_2001_ = v_isSharedCheck_2030_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_toApplicative_1998_);
lean_dec(v___x_1997_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2030_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_toFunctor_2002_; lean_object* v_toSeq_2003_; lean_object* v_toSeqLeft_2004_; lean_object* v_toSeqRight_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2028_; 
v_toFunctor_2002_ = lean_ctor_get(v_toApplicative_1998_, 0);
v_toSeq_2003_ = lean_ctor_get(v_toApplicative_1998_, 2);
v_toSeqLeft_2004_ = lean_ctor_get(v_toApplicative_1998_, 3);
v_toSeqRight_2005_ = lean_ctor_get(v_toApplicative_1998_, 4);
v_isSharedCheck_2028_ = !lean_is_exclusive(v_toApplicative_1998_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v_toApplicative_1998_, 1);
lean_dec(v_unused_2029_);
v___x_2007_ = v_toApplicative_1998_;
v_isShared_2008_ = v_isSharedCheck_2028_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_toSeqRight_2005_);
lean_inc(v_toSeqLeft_2004_);
lean_inc(v_toSeq_2003_);
lean_inc(v_toFunctor_2002_);
lean_dec(v_toApplicative_1998_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2028_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___f_2009_; lean_object* v___f_2010_; lean_object* v___f_2011_; lean_object* v___f_2012_; lean_object* v___x_2013_; lean_object* v___f_2014_; lean_object* v___f_2015_; lean_object* v___f_2016_; lean_object* v___x_2018_; 
v___f_2009_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__0));
v___f_2010_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__2_spec__4___closed__1));
lean_inc_ref(v_toFunctor_2002_);
v___f_2011_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2011_, 0, v_toFunctor_2002_);
v___f_2012_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2012_, 0, v_toFunctor_2002_);
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___f_2011_);
lean_ctor_set(v___x_2013_, 1, v___f_2012_);
v___f_2014_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2014_, 0, v_toSeqRight_2005_);
v___f_2015_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2015_, 0, v_toSeqLeft_2004_);
v___f_2016_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2016_, 0, v_toSeq_2003_);
if (v_isShared_2008_ == 0)
{
lean_ctor_set(v___x_2007_, 4, v___f_2014_);
lean_ctor_set(v___x_2007_, 3, v___f_2015_);
lean_ctor_set(v___x_2007_, 2, v___f_2016_);
lean_ctor_set(v___x_2007_, 1, v___f_2009_);
lean_ctor_set(v___x_2007_, 0, v___x_2013_);
v___x_2018_ = v___x_2007_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2013_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___f_2009_);
lean_ctor_set(v_reuseFailAlloc_2027_, 2, v___f_2016_);
lean_ctor_set(v_reuseFailAlloc_2027_, 3, v___f_2015_);
lean_ctor_set(v_reuseFailAlloc_2027_, 4, v___f_2014_);
v___x_2018_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___f_2010_);
lean_ctor_set(v___x_2000_, 0, v___x_2018_);
v___x_2020_ = v___x_2000_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2018_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___f_2010_);
v___x_2020_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_11231__overap_2024_; lean_object* v___x_2025_; 
v___x_2021_ = l_ReaderT_instMonad___redArg(v___x_2020_);
v___x_2022_ = lean_box(0);
v___x_2023_ = l_instInhabitedOfMonad___redArg(v___x_2021_, v___x_2022_);
v___x_11231__overap_2024_ = lean_panic_fn(v___x_2023_, v_msg_1965_);
lean_inc(v___y_1970_);
lean_inc_ref(v___y_1969_);
lean_inc(v___y_1968_);
lean_inc_ref(v___y_1967_);
lean_inc_ref(v___y_1966_);
v___x_2025_ = lean_apply_6(v___x_11231__overap_2024_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, lean_box(0));
return v___x_2025_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0___boxed(lean_object* v_msg_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v_msg_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec_ref(v___y_2039_);
return v_res_2045_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__0));
v___x_2048_ = l_Lean_stringToMessageData(v___x_2047_);
return v___x_2048_;
}
}
static lean_object* _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2050_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__6));
v___x_2051_ = lean_unsigned_to_nat(11u);
v___x_2052_ = lean_unsigned_to_nat(115u);
v___x_2053_ = ((lean_object*)(l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__2));
v___x_2054_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__4));
v___x_2055_ = l_mkPanicMessageWithDecl(v___x_2054_, v___x_2053_, v___x_2052_, v___x_2051_, v___x_2050_);
return v___x_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(lean_object* v_constName_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
lean_object* v___x_2071_; lean_object* v_env_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2071_ = lean_st_ref_get(v___y_2061_);
v_env_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc_ref(v_env_2072_);
lean_dec(v___x_2071_);
v___x_2073_ = 0;
lean_inc(v_constName_2056_);
v___x_2074_ = l_Lean_Environment_findAsync_x3f(v_env_2072_, v_constName_2056_, v___x_2073_);
if (lean_obj_tag(v___x_2074_) == 1)
{
lean_object* v_val_2075_; uint8_t v_kind_2076_; 
v_val_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref(v___x_2074_);
v_kind_2076_ = lean_ctor_get_uint8(v_val_2075_, sizeof(void*)*3);
if (v_kind_2076_ == 0)
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_2075_);
if (lean_obj_tag(v___x_2077_) == 1)
{
lean_object* v_val_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_dec(v_constName_2056_);
v_val_2078_ = lean_ctor_get(v___x_2077_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_2077_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_2077_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_val_2078_);
lean_dec(v___x_2077_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
lean_ctor_set_tag(v___x_2080_, 0);
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_val_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
else
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec_ref(v___x_2077_);
v___x_2086_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__3);
v___x_2087_ = l_panic___at___00Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0_spec__0(v___x_2086_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
if (lean_obj_tag(v___x_2087_) == 0)
{
lean_object* v_a_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2096_; 
v_a_2088_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2090_ = v___x_2087_;
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_a_2088_);
lean_dec(v___x_2087_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2096_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
if (lean_obj_tag(v_a_2088_) == 0)
{
lean_del_object(v___x_2090_);
goto v___jp_2063_;
}
else
{
lean_object* v_val_2092_; lean_object* v___x_2094_; 
lean_dec(v_constName_2056_);
v_val_2092_ = lean_ctor_get(v_a_2088_, 0);
lean_inc(v_val_2092_);
lean_dec_ref(v_a_2088_);
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v_val_2092_);
v___x_2094_ = v___x_2090_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_val_2092_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
lean_dec(v_constName_2056_);
v_a_2097_ = lean_ctor_get(v___x_2087_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2087_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2087_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2087_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2102_; 
if (v_isShared_2100_ == 0)
{
v___x_2102_ = v___x_2099_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_a_2097_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
else
{
lean_dec(v_val_2075_);
goto v___jp_2063_;
}
}
else
{
lean_dec(v___x_2074_);
goto v___jp_2063_;
}
v___jp_2063_:
{
lean_object* v___x_2064_; uint8_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2064_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_Elab_ComputedFields_isScalarField_spec__0___closed__1);
v___x_2065_ = 0;
v___x_2066_ = l_Lean_MessageData_ofConstName(v_constName_2056_, v___x_2065_);
v___x_2067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2064_);
lean_ctor_set(v___x_2067_, 1, v___x_2066_);
v___x_2068_ = lean_obj_once(&l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1, &l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1_once, _init_l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___closed__1);
v___x_2069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2067_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v___x_2070_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_validateComputedFields_spec__1___redArg(v___x_2069_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0___boxed(lean_object* v_constName_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v_constName_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn(lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_toInductiveVal_2122_; lean_object* v_toConstantVal_2123_; lean_object* v_lparams_2124_; lean_object* v_params_2125_; lean_object* v_compFieldVars_2126_; lean_object* v_numIndices_2127_; lean_object* v_ctors_2128_; lean_object* v_name_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_toInductiveVal_2122_ = lean_ctor_get(v_a_2116_, 0);
v_toConstantVal_2123_ = lean_ctor_get(v_toInductiveVal_2122_, 0);
v_lparams_2124_ = lean_ctor_get(v_a_2116_, 1);
v_params_2125_ = lean_ctor_get(v_a_2116_, 2);
v_compFieldVars_2126_ = lean_ctor_get(v_a_2116_, 4);
v_numIndices_2127_ = lean_ctor_get(v_toInductiveVal_2122_, 2);
v_ctors_2128_ = lean_ctor_get(v_toInductiveVal_2122_, 4);
v_name_2129_ = lean_ctor_get(v_toConstantVal_2123_, 0);
lean_inc(v_name_2129_);
v___x_2130_ = l_Lean_mkCasesOnName(v_name_2129_);
lean_inc(v___x_2130_);
v___x_2131_ = l_Lean_getConstInfoDefn___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__0(v___x_2130_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2131_);
v___x_2133_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_2129_);
v___x_2134_ = l_Lean_Name_append(v_name_2129_, v___x_2133_);
lean_inc(v___x_2134_);
v___x_2135_ = l_Lean_mkCasesOn(v___x_2134_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2196_; 
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v___x_2135_, 0);
lean_dec(v_unused_2197_);
v___x_2137_ = v___x_2135_;
v_isShared_2138_ = v_isSharedCheck_2196_;
goto v_resetjp_2136_;
}
else
{
lean_dec(v___x_2135_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2196_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_toConstantVal_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2192_; 
v_toConstantVal_2139_ = lean_ctor_get(v_a_2132_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_a_2132_);
if (v_isSharedCheck_2192_ == 0)
{
lean_object* v_unused_2193_; lean_object* v_unused_2194_; lean_object* v_unused_2195_; 
v_unused_2193_ = lean_ctor_get(v_a_2132_, 3);
lean_dec(v_unused_2193_);
v_unused_2194_ = lean_ctor_get(v_a_2132_, 2);
lean_dec(v_unused_2194_);
v_unused_2195_ = lean_ctor_get(v_a_2132_, 1);
lean_dec(v_unused_2195_);
v___x_2141_ = v_a_2132_;
v_isShared_2142_ = v_isSharedCheck_2192_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_toConstantVal_2139_);
lean_dec(v_a_2132_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2192_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_levelParams_2143_; lean_object* v_type_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2190_; 
v_levelParams_2143_ = lean_ctor_get(v_toConstantVal_2139_, 1);
v_type_2144_ = lean_ctor_get(v_toConstantVal_2139_, 2);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_toConstantVal_2139_);
if (v_isSharedCheck_2190_ == 0)
{
lean_object* v_unused_2191_; 
v_unused_2191_ = lean_ctor_get(v_toConstantVal_2139_, 0);
lean_dec(v_unused_2191_);
v___x_2146_ = v_toConstantVal_2139_;
v_isShared_2147_ = v_isSharedCheck_2190_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_type_2144_);
lean_inc(v_levelParams_2143_);
lean_dec(v_toConstantVal_2139_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2190_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; 
lean_inc_ref(v_type_2144_);
v___x_2148_ = l_Lean_Meta_instantiateForall(v_type_2144_, v_params_2125_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; lean_object* v___f_2151_; uint8_t v___x_2152_; lean_object* v___x_2153_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
v___x_2150_ = l_Lean_instInhabitedExpr;
lean_inc(v_levelParams_2143_);
lean_inc_ref(v_compFieldVars_2126_);
lean_inc(v_ctors_2128_);
lean_inc_ref(v_params_2125_);
lean_inc(v_lparams_2124_);
lean_inc(v_numIndices_2127_);
v___f_2151_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideCasesOn___lam__2___boxed), 16, 8);
lean_closure_set(v___f_2151_, 0, v_numIndices_2127_);
lean_closure_set(v___f_2151_, 1, v___x_2150_);
lean_closure_set(v___f_2151_, 2, v___x_2134_);
lean_closure_set(v___f_2151_, 3, v_lparams_2124_);
lean_closure_set(v___f_2151_, 4, v_params_2125_);
lean_closure_set(v___f_2151_, 5, v_ctors_2128_);
lean_closure_set(v___f_2151_, 6, v_compFieldVars_2126_);
lean_closure_set(v___f_2151_, 7, v_levelParams_2143_);
v___x_2152_ = 0;
v___x_2153_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2149_, v___f_2151_, v___x_2152_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2153_);
v___x_2155_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v___x_2130_);
v___x_2156_ = l_Lean_Name_append(v___x_2130_, v___x_2155_);
lean_inc(v___x_2156_);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2156_);
v___x_2158_ = v___x_2146_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2156_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_levelParams_2143_);
lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_type_2144_);
v___x_2158_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2159_ = lean_box(0);
v___x_2160_ = 0;
v___x_2161_ = lean_box(0);
lean_inc(v___x_2156_);
v___x_2162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2156_);
lean_ctor_set(v___x_2162_, 1, v___x_2161_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 3, v___x_2162_);
lean_ctor_set(v___x_2141_, 2, v___x_2159_);
lean_ctor_set(v___x_2141_, 1, v_a_2154_);
lean_ctor_set(v___x_2141_, 0, v___x_2158_);
v___x_2164_ = v___x_2141_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2158_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_a_2154_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v___x_2159_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
lean_object* v___x_2166_; 
lean_ctor_set_uint8(v___x_2164_, sizeof(void*)*4, v___x_2160_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set_tag(v___x_2137_, 1);
lean_ctor_set(v___x_2137_, 0, v___x_2164_);
v___x_2166_ = v___x_2137_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Lean_addDecl(v___x_2166_, v___x_2152_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2167_) == 0)
{
uint8_t v___x_2168_; lean_object* v___x_2169_; 
lean_dec_ref(v___x_2167_);
v___x_2168_ = 0;
lean_inc(v___x_2156_);
v___x_2169_ = l_Lean_Meta_setInlineAttribute(v___x_2156_, v___x_2168_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v___x_2170_; 
lean_dec_ref(v___x_2169_);
v___x_2170_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v___x_2130_, v___x_2156_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_, v_a_2120_);
lean_dec_ref(v_a_2116_);
return v___x_2170_;
}
else
{
lean_dec(v___x_2156_);
lean_dec(v___x_2130_);
lean_dec_ref(v_a_2116_);
return v___x_2169_;
}
}
else
{
lean_dec(v___x_2156_);
lean_dec(v___x_2130_);
lean_dec_ref(v_a_2116_);
return v___x_2167_;
}
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_del_object(v___x_2146_);
lean_dec_ref(v_type_2144_);
lean_dec(v_levelParams_2143_);
lean_del_object(v___x_2141_);
lean_del_object(v___x_2137_);
lean_dec(v___x_2130_);
lean_dec_ref(v_a_2116_);
v_a_2174_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2153_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2153_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_2146_);
lean_dec_ref(v_type_2144_);
lean_dec(v_levelParams_2143_);
lean_del_object(v___x_2141_);
lean_del_object(v___x_2137_);
lean_dec(v___x_2134_);
lean_dec(v___x_2130_);
lean_dec_ref(v_a_2116_);
v_a_2182_ = lean_ctor_get(v___x_2148_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2148_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2148_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_2134_);
lean_dec(v_a_2132_);
lean_dec(v___x_2130_);
lean_dec_ref(v_a_2116_);
return v___x_2135_;
}
}
else
{
lean_object* v_a_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2205_; 
lean_dec(v___x_2130_);
lean_dec_ref(v_a_2116_);
v_a_2198_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2200_ = v___x_2131_;
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_a_2198_);
lean_dec(v___x_2131_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2205_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2203_; 
if (v_isShared_2201_ == 0)
{
v___x_2203_ = v___x_2200_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_a_2198_);
v___x_2203_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
return v___x_2203_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideCasesOn___boxed(lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1(lean_object* v_inst_2213_, lean_object* v_R_2214_, lean_object* v_a_2215_, lean_object* v_b_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v_a_2215_, v_b_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(lean_object* v_00_u03b1_2218_, lean_object* v_name_2219_, uint8_t v_bi_2220_, lean_object* v_type_2221_, lean_object* v_k_2222_, uint8_t v_kind_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___redArg(v_name_2219_, v_bi_2220_, v_type_2221_, v_k_2222_, v_kind_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_name_2232_, lean_object* v_bi_2233_, lean_object* v_type_2234_, lean_object* v_k_2235_, lean_object* v_kind_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
uint8_t v_bi_boxed_2243_; uint8_t v_kind_boxed_2244_; lean_object* v_res_2245_; 
v_bi_boxed_2243_ = lean_unbox(v_bi_2233_);
v_kind_boxed_2244_ = lean_unbox(v_kind_2236_);
v_res_2245_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3_spec__4(v_00_u03b1_2231_, v_name_2232_, v_bi_boxed_2243_, v_type_2234_, v_k_2235_, v_kind_boxed_2244_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(lean_object* v_00_u03b1_2246_, lean_object* v_name_2247_, lean_object* v_type_2248_, lean_object* v_k_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v_name_2247_, v_type_2248_, v_k_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___boxed(lean_object* v_00_u03b1_2257_, lean_object* v_name_2258_, lean_object* v_type_2259_, lean_object* v_k_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3(v_00_u03b1_2257_, v_name_2258_, v_type_2259_, v_k_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec_ref(v___y_2261_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(lean_object* v_env_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg(v_env_2268_, v___y_2271_, v___y_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___boxed(lean_object* v_env_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8(v_env_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v___y_2277_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(lean_object* v___x_2284_, size_t v_sz_2285_, size_t v_i_2286_, lean_object* v_bs_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v___x_2293_; 
v___x_2293_ = lean_usize_dec_lt(v_i_2286_, v_sz_2285_);
if (v___x_2293_ == 0)
{
lean_object* v___x_2294_; 
lean_dec_ref(v___x_2284_);
v___x_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2294_, 0, v_bs_2287_);
return v___x_2294_;
}
else
{
lean_object* v_v_2295_; lean_object* v___x_2296_; 
v_v_2295_ = lean_array_uget_borrowed(v_bs_2287_, v_i_2286_);
lean_inc_ref(v___x_2284_);
lean_inc(v_v_2295_);
v___x_2296_ = l_Lean_Elab_ComputedFields_getComputedFieldValue(v_v_2295_, v___x_2284_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; lean_object* v_bs_x27_2299_; size_t v___x_2300_; size_t v___x_2301_; lean_object* v___x_2302_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2296_);
v___x_2298_ = lean_unsigned_to_nat(0u);
v_bs_x27_2299_ = lean_array_uset(v_bs_2287_, v_i_2286_, v___x_2298_);
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2286_, v___x_2300_);
v___x_2302_ = lean_array_uset(v_bs_x27_2299_, v_i_2286_, v_a_2297_);
v_i_2286_ = v___x_2301_;
v_bs_2287_ = v___x_2302_;
goto _start;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v_bs_2287_);
lean_dec_ref(v___x_2284_);
v_a_2304_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2296_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2296_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg___boxed(lean_object* v___x_2312_, lean_object* v_sz_2313_, lean_object* v_i_2314_, lean_object* v_bs_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
size_t v_sz_boxed_2321_; size_t v_i_boxed_2322_; lean_object* v_res_2323_; 
v_sz_boxed_2321_ = lean_unbox_usize(v_sz_2313_);
lean_dec(v_sz_2313_);
v_i_boxed_2322_ = lean_unbox_usize(v_i_2314_);
lean_dec(v_i_2314_);
v_res_2323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2312_, v_sz_boxed_2321_, v_i_boxed_2322_, v_bs_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(lean_object* v_head_2324_, lean_object* v_compFields_2325_, lean_object* v___x_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Lean_Elab_ComputedFields_isScalarField(v_head_2324_, v___y_2330_, v___y_2331_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2346_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2336_ = v___x_2333_;
v_isShared_2337_ = v_isSharedCheck_2346_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2333_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2346_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint8_t v___x_2338_; 
v___x_2338_ = lean_unbox(v_a_2334_);
lean_dec(v_a_2334_);
if (v___x_2338_ == 0)
{
size_t v_sz_2339_; size_t v___x_2340_; lean_object* v___x_2341_; 
lean_del_object(v___x_2336_);
v_sz_2339_ = lean_array_size(v_compFields_2325_);
v___x_2340_ = ((size_t)0ULL);
v___x_2341_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__0___redArg(v___x_2326_, v_sz_2339_, v___x_2340_, v_compFields_2325_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
return v___x_2341_;
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2344_; 
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_compFields_2325_);
v___x_2342_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2342_);
v___x_2344_ = v___x_2336_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec_ref(v___x_2326_);
lean_dec_ref(v_compFields_2325_);
v_a_2347_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2333_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2333_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0___boxed(lean_object* v_head_2355_, lean_object* v_compFields_2356_, lean_object* v___x_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg___lam__0(v_head_2355_, v_compFields_2356_, v___x_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(lean_object* v___y_2365_, uint8_t v_isExporting_2366_, lean_object* v___x_2367_, lean_object* v___y_2368_, lean_object* v___x_2369_, lean_object* v_a_x3f_2370_){
_start:
{
lean_object* v___x_2372_; lean_object* v_env_2373_; lean_object* v_nextMacroScope_2374_; lean_object* v_ngen_2375_; lean_object* v_auxDeclNGen_2376_; lean_object* v_traceState_2377_; lean_object* v_messages_2378_; lean_object* v_infoState_2379_; lean_object* v_snapshotTasks_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2405_; 
v___x_2372_ = lean_st_ref_take(v___y_2365_);
v_env_2373_ = lean_ctor_get(v___x_2372_, 0);
v_nextMacroScope_2374_ = lean_ctor_get(v___x_2372_, 1);
v_ngen_2375_ = lean_ctor_get(v___x_2372_, 2);
v_auxDeclNGen_2376_ = lean_ctor_get(v___x_2372_, 3);
v_traceState_2377_ = lean_ctor_get(v___x_2372_, 4);
v_messages_2378_ = lean_ctor_get(v___x_2372_, 6);
v_infoState_2379_ = lean_ctor_get(v___x_2372_, 7);
v_snapshotTasks_2380_ = lean_ctor_get(v___x_2372_, 8);
v_isSharedCheck_2405_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2405_ == 0)
{
lean_object* v_unused_2406_; 
v_unused_2406_ = lean_ctor_get(v___x_2372_, 5);
lean_dec(v_unused_2406_);
v___x_2382_ = v___x_2372_;
v_isShared_2383_ = v_isSharedCheck_2405_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_snapshotTasks_2380_);
lean_inc(v_infoState_2379_);
lean_inc(v_messages_2378_);
lean_inc(v_traceState_2377_);
lean_inc(v_auxDeclNGen_2376_);
lean_inc(v_ngen_2375_);
lean_inc(v_nextMacroScope_2374_);
lean_inc(v_env_2373_);
lean_dec(v___x_2372_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2405_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2384_; lean_object* v___x_2386_; 
v___x_2384_ = l_Lean_Environment_setExporting(v_env_2373_, v_isExporting_2366_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 5, v___x_2367_);
lean_ctor_set(v___x_2382_, 0, v___x_2384_);
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2384_);
lean_ctor_set(v_reuseFailAlloc_2404_, 1, v_nextMacroScope_2374_);
lean_ctor_set(v_reuseFailAlloc_2404_, 2, v_ngen_2375_);
lean_ctor_set(v_reuseFailAlloc_2404_, 3, v_auxDeclNGen_2376_);
lean_ctor_set(v_reuseFailAlloc_2404_, 4, v_traceState_2377_);
lean_ctor_set(v_reuseFailAlloc_2404_, 5, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2404_, 6, v_messages_2378_);
lean_ctor_set(v_reuseFailAlloc_2404_, 7, v_infoState_2379_);
lean_ctor_set(v_reuseFailAlloc_2404_, 8, v_snapshotTasks_2380_);
v___x_2386_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v_mctx_2389_; lean_object* v_zetaDeltaFVarIds_2390_; lean_object* v_postponed_2391_; lean_object* v_diag_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2402_; 
v___x_2387_ = lean_st_ref_set(v___y_2365_, v___x_2386_);
v___x_2388_ = lean_st_ref_take(v___y_2368_);
v_mctx_2389_ = lean_ctor_get(v___x_2388_, 0);
v_zetaDeltaFVarIds_2390_ = lean_ctor_get(v___x_2388_, 2);
v_postponed_2391_ = lean_ctor_get(v___x_2388_, 3);
v_diag_2392_ = lean_ctor_get(v___x_2388_, 4);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2402_ == 0)
{
lean_object* v_unused_2403_; 
v_unused_2403_ = lean_ctor_get(v___x_2388_, 1);
lean_dec(v_unused_2403_);
v___x_2394_ = v___x_2388_;
v_isShared_2395_ = v_isSharedCheck_2402_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_diag_2392_);
lean_inc(v_postponed_2391_);
lean_inc(v_zetaDeltaFVarIds_2390_);
lean_inc(v_mctx_2389_);
lean_dec(v___x_2388_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2402_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 1, v___x_2369_);
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_mctx_2389_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v___x_2369_);
lean_ctor_set(v_reuseFailAlloc_2401_, 2, v_zetaDeltaFVarIds_2390_);
lean_ctor_set(v_reuseFailAlloc_2401_, 3, v_postponed_2391_);
lean_ctor_set(v_reuseFailAlloc_2401_, 4, v_diag_2392_);
v___x_2397_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = lean_st_ref_set(v___y_2368_, v___x_2397_);
v___x_2399_ = lean_box(0);
v___x_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
return v___x_2400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_2407_, lean_object* v_isExporting_2408_, lean_object* v___x_2409_, lean_object* v___y_2410_, lean_object* v___x_2411_, lean_object* v_a_x3f_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v_isExporting_boxed_2414_; lean_object* v_res_2415_; 
v_isExporting_boxed_2414_ = lean_unbox(v_isExporting_2408_);
v_res_2415_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2407_, v_isExporting_boxed_2414_, v___x_2409_, v___y_2410_, v___x_2411_, v_a_x3f_2412_);
lean_dec(v_a_x3f_2412_);
lean_dec(v___y_2410_);
lean_dec(v___y_2407_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg(lean_object* v_x_2416_, uint8_t v_isExporting_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; lean_object* v_env_2425_; uint8_t v_isExporting_2426_; lean_object* v___x_2427_; lean_object* v_env_2428_; lean_object* v_nextMacroScope_2429_; lean_object* v_ngen_2430_; lean_object* v_auxDeclNGen_2431_; lean_object* v_traceState_2432_; lean_object* v_messages_2433_; lean_object* v_infoState_2434_; lean_object* v_snapshotTasks_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2489_; 
v___x_2424_ = lean_st_ref_get(v___y_2422_);
v_env_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc_ref(v_env_2425_);
lean_dec(v___x_2424_);
v_isExporting_2426_ = lean_ctor_get_uint8(v_env_2425_, sizeof(void*)*8);
lean_dec_ref(v_env_2425_);
v___x_2427_ = lean_st_ref_take(v___y_2422_);
v_env_2428_ = lean_ctor_get(v___x_2427_, 0);
v_nextMacroScope_2429_ = lean_ctor_get(v___x_2427_, 1);
v_ngen_2430_ = lean_ctor_get(v___x_2427_, 2);
v_auxDeclNGen_2431_ = lean_ctor_get(v___x_2427_, 3);
v_traceState_2432_ = lean_ctor_get(v___x_2427_, 4);
v_messages_2433_ = lean_ctor_get(v___x_2427_, 6);
v_infoState_2434_ = lean_ctor_get(v___x_2427_, 7);
v_snapshotTasks_2435_ = lean_ctor_get(v___x_2427_, 8);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2489_ == 0)
{
lean_object* v_unused_2490_; 
v_unused_2490_ = lean_ctor_get(v___x_2427_, 5);
lean_dec(v_unused_2490_);
v___x_2437_ = v___x_2427_;
v_isShared_2438_ = v_isSharedCheck_2489_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_snapshotTasks_2435_);
lean_inc(v_infoState_2434_);
lean_inc(v_messages_2433_);
lean_inc(v_traceState_2432_);
lean_inc(v_auxDeclNGen_2431_);
lean_inc(v_ngen_2430_);
lean_inc(v_nextMacroScope_2429_);
lean_inc(v_env_2428_);
lean_dec(v___x_2427_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2489_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2442_; 
v___x_2439_ = l_Lean_Environment_setExporting(v_env_2428_, v_isExporting_2417_);
v___x_2440_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__2);
if (v_isShared_2438_ == 0)
{
lean_ctor_set(v___x_2437_, 5, v___x_2440_);
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2442_ = v___x_2437_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2439_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v_nextMacroScope_2429_);
lean_ctor_set(v_reuseFailAlloc_2488_, 2, v_ngen_2430_);
lean_ctor_set(v_reuseFailAlloc_2488_, 3, v_auxDeclNGen_2431_);
lean_ctor_set(v_reuseFailAlloc_2488_, 4, v_traceState_2432_);
lean_ctor_set(v_reuseFailAlloc_2488_, 5, v___x_2440_);
lean_ctor_set(v_reuseFailAlloc_2488_, 6, v_messages_2433_);
lean_ctor_set(v_reuseFailAlloc_2488_, 7, v_infoState_2434_);
lean_ctor_set(v_reuseFailAlloc_2488_, 8, v_snapshotTasks_2435_);
v___x_2442_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v_mctx_2445_; lean_object* v_zetaDeltaFVarIds_2446_; lean_object* v_postponed_2447_; lean_object* v_diag_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2486_; 
v___x_2443_ = lean_st_ref_set(v___y_2422_, v___x_2442_);
v___x_2444_ = lean_st_ref_take(v___y_2420_);
v_mctx_2445_ = lean_ctor_get(v___x_2444_, 0);
v_zetaDeltaFVarIds_2446_ = lean_ctor_get(v___x_2444_, 2);
v_postponed_2447_ = lean_ctor_get(v___x_2444_, 3);
v_diag_2448_ = lean_ctor_get(v___x_2444_, 4);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v___x_2444_, 1);
lean_dec(v_unused_2487_);
v___x_2450_ = v___x_2444_;
v_isShared_2451_ = v_isSharedCheck_2486_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_diag_2448_);
lean_inc(v_postponed_2447_);
lean_inc(v_zetaDeltaFVarIds_2446_);
lean_inc(v_mctx_2445_);
lean_dec(v___x_2444_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2486_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2452_ = lean_obj_once(&l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3, &l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3_once, _init_l_Lean_setEnv___at___00Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6_spec__8___redArg___closed__3);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2452_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_mctx_2445_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_zetaDeltaFVarIds_2446_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_postponed_2447_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_diag_2448_);
v___x_2454_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v_r_2456_; 
v___x_2455_ = lean_st_ref_set(v___y_2420_, v___x_2454_);
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
lean_inc_ref(v___y_2418_);
v_r_2456_ = lean_apply_6(v_x_2416_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, lean_box(0));
if (lean_obj_tag(v_r_2456_) == 0)
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2473_; 
v_a_2457_ = lean_ctor_get(v_r_2456_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_r_2456_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2459_ = v_r_2456_;
v_isShared_2460_ = v_isSharedCheck_2473_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v_r_2456_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2473_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
lean_inc(v_a_2457_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set_tag(v___x_2459_, 1);
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
lean_object* v___x_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
v___x_2463_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2422_, v_isExporting_2426_, v___x_2440_, v___y_2420_, v___x_2452_, v___x_2462_);
lean_dec_ref(v___x_2462_);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2470_ == 0)
{
lean_object* v_unused_2471_; 
v_unused_2471_ = lean_ctor_get(v___x_2463_, 0);
lean_dec(v_unused_2471_);
v___x_2465_ = v___x_2463_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_dec(v___x_2463_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v_a_2457_);
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2457_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2483_; 
v_a_2474_ = lean_ctor_get(v_r_2456_, 0);
lean_inc(v_a_2474_);
lean_dec_ref(v_r_2456_);
v___x_2475_ = lean_box(0);
v___x_2476_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1_spec__1___redArg___lam__0(v___y_2422_, v_isExporting_2426_, v___x_2440_, v___y_2420_, v___x_2452_, v___x_2475_);
v_isSharedCheck_2483_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v___x_2476_, 0);
lean_dec(v_unused_2484_);
v___x_2478_ = v___x_2476_;
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
else
{
lean_dec(v___x_2476_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2483_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2481_; 
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 1);
lean_ctor_set(v___x_2478_, 0, v_a_2474_);
v___x_2481_ = v___x_2478_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_a_2474_);
v___x_2481_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
return v___x_2481_;
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
lean_dec_ref(v___x_2541_);
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
lean_dec_ref(v___x_2543_);
v___x_2545_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
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
lean_dec_ref(v___x_2551_);
v___x_2553_ = 0;
v___x_2554_ = 1;
v___x_2555_ = l_Lean_Meta_mkLambdaFVars(v___x_2537_, v_a_2552_, v___x_2553_, v___x_2540_, v___x_2553_, v___x_2540_, v___x_2554_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
lean_dec_ref(v___x_2537_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref(v___x_2555_);
v___x_2557_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_head_2524_);
v___x_2558_ = l_Lean_Name_append(v_head_2524_, v___x_2557_);
lean_inc(v___x_2558_);
v___x_2559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v_levelParams_2527_);
lean_ctor_set(v___x_2559_, 2, v_a_2544_);
v___x_2560_ = lean_box(0);
v___x_2561_ = 0;
v___x_2562_ = lean_box(0);
lean_inc(v___x_2558_);
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
lean_dec_ref(v___x_2566_);
lean_inc(v___x_2558_);
lean_inc(v_head_2524_);
v___x_2567_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_head_2524_, v___x_2558_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_, v___y_2535_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v___x_2568_; 
lean_dec_ref(v___x_2567_);
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
lean_inc(v_head_2649_);
v_tail_2650_ = lean_ctor_get(v_as_x27_2640_, 1);
lean_inc(v_tail_2650_);
lean_dec_ref(v_as_x27_2640_);
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
lean_dec_ref(v___x_2653_);
v___x_2655_ = lean_box(0);
lean_inc(v_levelParams_2639_);
lean_inc(v_lparams_2636_);
lean_inc_ref(v_compFields_2638_);
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
lean_dec_ref(v___x_2658_);
v_as_x27_2640_ = v_tail_2650_;
v_b_2641_ = v___x_2655_;
goto _start;
}
else
{
lean_dec(v_tail_2650_);
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
lean_dec(v_tail_2650_);
lean_dec(v_head_2649_);
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
lean_inc(v_lparams_2689_);
v_params_2690_ = lean_ctor_get(v_a_2681_, 2);
lean_inc_ref(v_params_2690_);
v_compFields_2691_ = lean_ctor_get(v_a_2681_, 3);
lean_inc_ref(v_compFields_2691_);
v_ctors_2692_ = lean_ctor_get(v_toInductiveVal_2687_, 4);
lean_inc(v_ctors_2692_);
v_levelParams_2693_ = lean_ctor_get(v_toConstantVal_2688_, 1);
lean_inc(v_levelParams_2693_);
v___x_2694_ = lean_box(0);
v___x_2695_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__2___redArg(v_lparams_2689_, v_params_2690_, v_compFields_2691_, v_levelParams_2693_, v_ctors_2692_, v___x_2694_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_);
lean_dec_ref(v_a_2681_);
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
lean_dec_ref(v___x_2823_);
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
lean_dec_ref(v___x_2833_);
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
uint8_t v___x_14619__boxed_2861_; uint8_t v___x_14622__boxed_2862_; lean_object* v_res_2863_; 
v___x_14619__boxed_2861_ = lean_unbox(v___x_2848_);
v___x_14622__boxed_2862_ = lean_unbox(v___x_2852_);
v_res_2863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0(v_v_2845_, v_compFieldVars_2846_, v___x_2847_, v___x_14619__boxed_2861_, v_params_2849_, v___x_2850_, v_a_2851_, v___x_14622__boxed_2862_, v_fields_2853_, v_x_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(lean_object* v_lparams_2864_, lean_object* v_compFieldVars_2865_, lean_object* v___x_2866_, lean_object* v_params_2867_, lean_object* v_a_2868_, uint8_t v___x_2869_, size_t v_sz_2870_, size_t v_i_2871_, lean_object* v_bs_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_){
_start:
{
uint8_t v___x_2879_; 
v___x_2879_ = lean_usize_dec_lt(v_i_2871_, v_sz_2870_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; 
lean_dec(v_a_2868_);
lean_dec_ref(v_params_2867_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v_compFieldVars_2865_);
lean_dec(v_lparams_2864_);
v___x_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2880_, 0, v_bs_2872_);
return v___x_2880_;
}
else
{
lean_object* v_v_2881_; lean_object* v___x_2882_; lean_object* v_bs_x27_2883_; lean_object* v___y_2885_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v_v_2881_ = lean_array_uget(v_bs_2872_, v_i_2871_);
v___x_2882_ = lean_unsigned_to_nat(0u);
v_bs_x27_2883_ = lean_array_uset(v_bs_2872_, v_i_2871_, v___x_2882_);
lean_inc(v_lparams_2864_);
lean_inc(v_v_2881_);
v___x_2899_ = l_Lean_mkConst(v_v_2881_, v_lparams_2864_);
lean_inc_ref(v___x_2899_);
v___x_2900_ = l_Lean_mkAppN(v___x_2899_, v_params_2867_);
lean_inc(v___y_2877_);
lean_inc_ref(v___y_2876_);
lean_inc(v___y_2875_);
lean_inc_ref(v___y_2874_);
v___x_2901_ = lean_infer_type(v___x_2900_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___f_2905_; lean_object* v___x_2906_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
v___x_2903_ = lean_box(v___x_2879_);
v___x_2904_ = lean_box(v___x_2869_);
lean_inc(v_a_2868_);
lean_inc_ref(v_params_2867_);
lean_inc_ref(v___x_2866_);
lean_inc_ref(v_compFieldVars_2865_);
v___f_2905_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___lam__0___boxed), 16, 8);
lean_closure_set(v___f_2905_, 0, v_v_2881_);
lean_closure_set(v___f_2905_, 1, v_compFieldVars_2865_);
lean_closure_set(v___f_2905_, 2, v___x_2866_);
lean_closure_set(v___f_2905_, 3, v___x_2903_);
lean_closure_set(v___f_2905_, 4, v_params_2867_);
lean_closure_set(v___f_2905_, 5, v___x_2899_);
lean_closure_set(v___f_2905_, 6, v_a_2868_);
lean_closure_set(v___f_2905_, 7, v___x_2904_);
v___x_2906_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkImplType_spec__0___redArg(v_a_2902_, v___f_2905_, v___x_2869_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
v___y_2885_ = v___x_2906_;
goto v___jp_2884_;
}
else
{
lean_dec_ref(v___x_2899_);
lean_dec(v_v_2881_);
v___y_2885_ = v___x_2901_;
goto v___jp_2884_;
}
v___jp_2884_:
{
if (lean_obj_tag(v___y_2885_) == 0)
{
lean_object* v_a_2886_; size_t v___x_2887_; size_t v___x_2888_; lean_object* v___x_2889_; 
v_a_2886_ = lean_ctor_get(v___y_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref(v___y_2885_);
v___x_2887_ = ((size_t)1ULL);
v___x_2888_ = lean_usize_add(v_i_2871_, v___x_2887_);
v___x_2889_ = lean_array_uset(v_bs_x27_2883_, v_i_2871_, v_a_2886_);
v_i_2871_ = v___x_2888_;
v_bs_2872_ = v___x_2889_;
goto _start;
}
else
{
lean_object* v_a_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2898_; 
lean_dec_ref(v_bs_x27_2883_);
lean_dec(v_a_2868_);
lean_dec_ref(v_params_2867_);
lean_dec_ref(v___x_2866_);
lean_dec_ref(v_compFieldVars_2865_);
lean_dec(v_lparams_2864_);
v_a_2891_ = lean_ctor_get(v___y_2885_, 0);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___y_2885_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2893_ = v___y_2885_;
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_a_2891_);
lean_dec(v___y_2885_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2898_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2896_; 
if (v_isShared_2894_ == 0)
{
v___x_2896_ = v___x_2893_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_a_2891_);
v___x_2896_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
return v___x_2896_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed(lean_object* v_lparams_2907_, lean_object* v_compFieldVars_2908_, lean_object* v___x_2909_, lean_object* v_params_2910_, lean_object* v_a_2911_, lean_object* v___x_2912_, lean_object* v_sz_2913_, lean_object* v_i_2914_, lean_object* v_bs_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_){
_start:
{
uint8_t v___x_14705__boxed_2922_; size_t v_sz_boxed_2923_; size_t v_i_boxed_2924_; lean_object* v_res_2925_; 
v___x_14705__boxed_2922_ = lean_unbox(v___x_2912_);
v_sz_boxed_2923_ = lean_unbox_usize(v_sz_2913_);
lean_dec(v_sz_2913_);
v_i_boxed_2924_ = lean_unbox_usize(v_i_2914_);
lean_dec(v_i_2914_);
v_res_2925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0(v_lparams_2907_, v_compFieldVars_2908_, v___x_2909_, v_params_2910_, v_a_2911_, v___x_14705__boxed_2922_, v_sz_boxed_2923_, v_i_boxed_2924_, v_bs_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec(v___y_2920_);
lean_dec_ref(v___y_2919_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(size_t v_sz_2926_, size_t v_i_2927_, lean_object* v_bs_2928_){
_start:
{
uint8_t v___x_2929_; 
v___x_2929_ = lean_usize_dec_lt(v_i_2927_, v_sz_2926_);
if (v___x_2929_ == 0)
{
return v_bs_2928_;
}
else
{
lean_object* v_v_2930_; lean_object* v___x_2931_; lean_object* v_bs_x27_2932_; lean_object* v___x_2933_; size_t v___x_2934_; size_t v___x_2935_; lean_object* v___x_2936_; 
v_v_2930_ = lean_array_uget(v_bs_2928_, v_i_2927_);
v___x_2931_ = lean_unsigned_to_nat(0u);
v_bs_x27_2932_ = lean_array_uset(v_bs_2928_, v_i_2927_, v___x_2931_);
v___x_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2933_, 0, v_v_2930_);
v___x_2934_ = ((size_t)1ULL);
v___x_2935_ = lean_usize_add(v_i_2927_, v___x_2934_);
v___x_2936_ = lean_array_uset(v_bs_x27_2932_, v_i_2927_, v___x_2933_);
v_i_2927_ = v___x_2935_;
v_bs_2928_ = v___x_2936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1___boxed(lean_object* v_sz_2938_, lean_object* v_i_2939_, lean_object* v_bs_2940_){
_start:
{
size_t v_sz_boxed_2941_; size_t v_i_boxed_2942_; lean_object* v_res_2943_; 
v_sz_boxed_2941_ = lean_unbox_usize(v_sz_2938_);
lean_dec(v_sz_2938_);
v_i_boxed_2942_ = lean_unbox_usize(v_i_2939_);
lean_dec(v_i_2939_);
v_res_2943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_boxed_2941_, v_i_boxed_2942_, v_bs_2940_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(lean_object* v_ctors_2946_, lean_object* v_lparams_2947_, lean_object* v_compFieldVars_2948_, lean_object* v_params_2949_, lean_object* v_val_2950_, lean_object* v___x_2951_, lean_object* v_indices_2952_, lean_object* v_xImpl_2953_, lean_object* v___x_2954_, lean_object* v_levelParams_2955_, lean_object* v_as_2956_, size_t v_sz_2957_, size_t v_i_2958_, lean_object* v_b_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v_a_2967_; uint8_t v___x_2971_; 
v___x_2971_ = lean_usize_dec_lt(v_i_2958_, v_sz_2957_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; 
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v_b_2959_);
return v___x_2972_;
}
else
{
lean_object* v_array_2973_; lean_object* v_start_2974_; lean_object* v_stop_2975_; uint8_t v___x_2976_; 
v_array_2973_ = lean_ctor_get(v_b_2959_, 0);
v_start_2974_ = lean_ctor_get(v_b_2959_, 1);
v_stop_2975_ = lean_ctor_get(v_b_2959_, 2);
v___x_2976_ = lean_nat_dec_lt(v_start_2974_, v_stop_2975_);
if (v___x_2976_ == 0)
{
lean_object* v___x_2977_; 
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v___x_2977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2977_, 0, v_b_2959_);
return v___x_2977_;
}
else
{
lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3160_; 
lean_inc(v_stop_2975_);
lean_inc(v_start_2974_);
lean_inc_ref(v_array_2973_);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_b_2959_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; lean_object* v_unused_3162_; lean_object* v_unused_3163_; 
v_unused_3161_ = lean_ctor_get(v_b_2959_, 2);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_b_2959_, 1);
lean_dec(v_unused_3162_);
v_unused_3163_ = lean_ctor_get(v_b_2959_, 0);
lean_dec(v_unused_3163_);
v___x_2979_ = v_b_2959_;
v_isShared_2980_ = v_isSharedCheck_3160_;
goto v_resetjp_2978_;
}
else
{
lean_dec(v_b_2959_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3160_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; lean_object* v_env_2982_; lean_object* v___x_2983_; lean_object* v_a_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2988_; 
v___x_2981_ = lean_st_ref_get(v___y_2964_);
v_env_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc_ref(v_env_2982_);
lean_dec(v___x_2981_);
v___x_2983_ = lean_array_fget(v_array_2973_, v_start_2974_);
v_a_2984_ = lean_array_uget_borrowed(v_as_2956_, v_i_2958_);
v___x_2985_ = lean_unsigned_to_nat(1u);
v___x_2986_ = lean_nat_add(v_start_2974_, v___x_2985_);
lean_dec(v_start_2974_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 1, v___x_2986_);
v___x_2988_ = v___x_2979_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_array_2973_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_2986_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_stop_2975_);
v___x_2988_ = v_reuseFailAlloc_3159_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
uint8_t v___x_2989_; 
lean_inc(v_a_2984_);
v___x_2989_ = l_Lean_isExtern(v_env_2982_, v_a_2984_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; size_t v_sz_2991_; size_t v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
lean_inc(v_ctors_2946_);
v___x_2990_ = lean_array_mk(v_ctors_2946_);
v_sz_2991_ = lean_array_size(v___x_2990_);
v___x_2992_ = ((size_t)0ULL);
v___x_2993_ = lean_box(v___x_2989_);
v___x_2994_ = lean_box_usize(v_sz_2991_);
v___x_2995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_2984_);
lean_inc_ref(v_params_2949_);
lean_inc(v___x_2983_);
lean_inc_ref(v_compFieldVars_2948_);
lean_inc(v_lparams_2947_);
v___x_2996_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_2996_, 0, v_lparams_2947_);
lean_closure_set(v___x_2996_, 1, v_compFieldVars_2948_);
lean_closure_set(v___x_2996_, 2, v___x_2983_);
lean_closure_set(v___x_2996_, 3, v_params_2949_);
lean_closure_set(v___x_2996_, 4, v_a_2984_);
lean_closure_set(v___x_2996_, 5, v___x_2993_);
lean_closure_set(v___x_2996_, 6, v___x_2994_);
lean_closure_set(v___x_2996_, 7, v___x_2995_);
lean_closure_set(v___x_2996_, 8, v___x_2990_);
v___x_2997_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_2996_, v___x_2976_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc(v_a_2998_);
lean_dec_ref(v___x_2997_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
lean_inc(v___x_2983_);
v___x_2999_ = lean_infer_type(v___x_2983_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v_a_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; 
v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
lean_inc(v_a_3000_);
lean_dec_ref(v___x_2999_);
v___x_3001_ = lean_mk_empty_array_with_capacity(v___x_2985_);
lean_inc_ref(v_val_2950_);
lean_inc_ref(v___x_3001_);
v___x_3002_ = lean_array_push(v___x_3001_, v_val_2950_);
lean_inc_ref(v___x_2951_);
v___x_3003_ = l_Array_append___redArg(v___x_2951_, v___x_3002_);
lean_dec_ref(v___x_3002_);
v___x_3004_ = 1;
v___x_3005_ = l_Lean_Meta_mkForallFVars(v___x_3003_, v_a_3000_, v___x_2989_, v___x_2976_, v___x_2976_, v___x_3004_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3005_) == 0)
{
lean_object* v_a_3006_; lean_object* v___x_3007_; 
v_a_3006_ = lean_ctor_get(v___x_3005_, 0);
lean_inc(v_a_3006_);
lean_dec_ref(v___x_3005_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
v___x_3007_ = lean_infer_type(v___x_2983_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref(v___x_3007_);
lean_inc_ref(v_xImpl_2953_);
lean_inc_ref(v_indices_2952_);
v___x_3009_ = lean_array_push(v_indices_2952_, v_xImpl_2953_);
v___x_3010_ = l_Lean_Meta_mkLambdaFVars(v___x_3009_, v_a_3008_, v___x_2989_, v___x_2976_, v___x_2989_, v___x_2976_, v___x_3004_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec_ref(v___x_3009_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_object* v_a_3011_; lean_object* v___x_3012_; 
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref(v___x_3010_);
lean_inc(v___y_2964_);
lean_inc_ref(v___y_2963_);
lean_inc(v___y_2962_);
lean_inc_ref(v___y_2961_);
lean_inc_ref(v_xImpl_2953_);
v___x_3012_ = lean_infer_type(v_xImpl_2953_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc(v_a_3013_);
lean_dec_ref(v___x_3012_);
lean_inc_ref(v_val_2950_);
v___x_3014_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3013_, v_val_2950_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; size_t v_sz_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref(v___x_3014_);
lean_inc(v___x_2954_);
v___x_3016_ = l_Lean_mkCasesOnName(v___x_2954_);
lean_inc_ref(v___x_3001_);
v___x_3017_ = lean_array_push(v___x_3001_, v_a_3011_);
lean_inc_ref(v_params_2949_);
v___x_3018_ = l_Array_append___redArg(v_params_2949_, v___x_3017_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = l_Array_append___redArg(v___x_3018_, v_indices_2952_);
v___x_3020_ = lean_array_push(v___x_3001_, v_a_3015_);
v___x_3021_ = l_Array_append___redArg(v___x_3019_, v___x_3020_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = l_Array_append___redArg(v___x_3021_, v_a_2998_);
lean_dec(v_a_2998_);
v_sz_3023_ = lean_array_size(v___x_3022_);
v___x_3024_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3023_, v___x_2992_, v___x_3022_);
v___x_3025_ = l_Lean_Meta_mkAppOptM(v___x_3016_, v___x_3024_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_object* v_a_3026_; lean_object* v___x_3027_; 
v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_a_3026_);
lean_dec_ref(v___x_3025_);
v___x_3027_ = l_Lean_Meta_mkLambdaFVars(v___x_3003_, v_a_3026_, v___x_2989_, v___x_2976_, v___x_2989_, v___x_2976_, v___x_3004_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
lean_dec_ref(v___x_3003_);
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref(v___x_3027_);
v___x_3029_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_2984_);
v___x_3030_ = l_Lean_Name_append(v_a_2984_, v___x_3029_);
lean_inc(v_levelParams_2955_);
lean_inc(v___x_3030_);
v___x_3046_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3030_);
lean_ctor_set(v___x_3046_, 1, v_levelParams_2955_);
lean_ctor_set(v___x_3046_, 2, v_a_3006_);
v___x_3047_ = lean_box(0);
v___x_3048_ = 0;
v___x_3049_ = lean_box(0);
lean_inc(v___x_3030_);
v___x_3050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3030_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3051_, 0, v___x_3046_);
lean_ctor_set(v___x_3051_, 1, v_a_3028_);
lean_ctor_set(v___x_3051_, 2, v___x_3047_);
lean_ctor_set(v___x_3051_, 3, v___x_3050_);
lean_ctor_set_uint8(v___x_3051_, sizeof(void*)*4, v___x_3048_);
v___x_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
v___x_3053_ = l_Lean_addDecl(v___x_3052_, v___x_2989_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v___x_3054_; lean_object* v_env_3055_; lean_object* v___x_3056_; 
lean_dec_ref(v___x_3053_);
v___x_3054_ = lean_st_ref_get(v___y_2964_);
v_env_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc_ref(v_env_3055_);
lean_dec(v___x_3054_);
lean_inc(v_a_2984_);
v___x_3056_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3055_, v_a_2984_);
if (lean_obj_tag(v___x_3056_) == 1)
{
lean_object* v_val_3057_; uint8_t v___x_3058_; lean_object* v___x_3059_; 
v_val_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref(v___x_3056_);
v___x_3058_ = lean_unbox(v_val_3057_);
lean_dec(v_val_3057_);
lean_inc(v___x_3030_);
v___x_3059_ = l_Lean_Meta_setInlineAttribute(v___x_3030_, v___x_3058_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_dec_ref(v___x_3059_);
v___y_3032_ = v___y_2960_;
v___y_3033_ = v___y_2961_;
v___y_3034_ = v___y_2962_;
v___y_3035_ = v___y_2963_;
v___y_3036_ = v___y_2964_;
goto v___jp_3031_;
}
else
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3067_; 
lean_dec(v___x_3030_);
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3067_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3067_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3067_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3065_; 
if (v_isShared_3063_ == 0)
{
v___x_3065_ = v___x_3062_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3066_; 
v_reuseFailAlloc_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_a_3060_);
v___x_3065_ = v_reuseFailAlloc_3066_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
return v___x_3065_;
}
}
}
}
else
{
lean_dec(v___x_3056_);
v___y_3032_ = v___y_2960_;
v___y_3033_ = v___y_2961_;
v___y_3034_ = v___y_2962_;
v___y_3035_ = v___y_2963_;
v___y_3036_ = v___y_2964_;
goto v___jp_3031_;
}
}
else
{
lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec(v___x_3030_);
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3068_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3053_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3053_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
v___jp_3031_:
{
lean_object* v___x_3037_; 
lean_inc(v_a_2984_);
v___x_3037_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_2984_, v___x_3030_, v___y_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_dec_ref(v___x_3037_);
v_a_2967_ = v___x_2988_;
goto v___jp_2966_;
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
else
{
lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v_a_3006_);
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3076_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3027_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3027_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec(v_a_3006_);
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3084_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3025_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3025_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3099_; 
lean_dec(v_a_3011_);
lean_dec(v_a_3006_);
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_3001_);
lean_dec(v_a_2998_);
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3092_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3099_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3099_ == 0)
{
v___x_3094_ = v___x_3014_;
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3014_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3099_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v___x_3097_; 
if (v_isShared_3095_ == 0)
{
v___x_3097_ = v___x_3094_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3098_; 
v_reuseFailAlloc_3098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3098_, 0, v_a_3092_);
v___x_3097_ = v_reuseFailAlloc_3098_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
return v___x_3097_;
}
}
}
}
else
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v_a_3011_);
lean_dec(v_a_3006_);
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_3001_);
lean_dec(v_a_2998_);
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3100_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3102_ = v___x_3012_;
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3012_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3107_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3105_; 
if (v_isShared_3103_ == 0)
{
v___x_3105_ = v___x_3102_;
goto v_reusejp_3104_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_a_3100_);
v___x_3105_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3104_;
}
v_reusejp_3104_:
{
return v___x_3105_;
}
}
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_a_3006_);
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_3001_);
lean_dec(v_a_2998_);
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3108_ = lean_ctor_get(v___x_3010_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3010_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3010_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3010_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v_a_3006_);
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_3001_);
lean_dec(v_a_2998_);
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3116_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3007_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3007_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec_ref(v___x_3003_);
lean_dec_ref(v___x_3001_);
lean_dec(v_a_2998_);
lean_dec_ref(v___x_2988_);
lean_dec(v___x_2983_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3124_ = lean_ctor_get(v___x_3005_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3005_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3005_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec(v_a_2998_);
lean_dec_ref(v___x_2988_);
lean_dec(v___x_2983_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3132_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_2999_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_2999_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec_ref(v___x_2988_);
lean_dec(v___x_2983_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3140_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_2997_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_2997_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec(v___x_2983_);
v___x_3148_ = lean_mk_empty_array_with_capacity(v___x_2985_);
lean_inc(v_a_2984_);
v___x_3149_ = lean_array_push(v___x_3148_, v_a_2984_);
v___x_3150_ = l_Lean_compileDecls(v___x_3149_, v___x_2976_, v___y_2963_, v___y_2964_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_dec_ref(v___x_3150_);
v_a_2967_ = v___x_2988_;
goto v___jp_2966_;
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
lean_dec_ref(v___x_2988_);
lean_dec(v_levelParams_2955_);
lean_dec(v___x_2954_);
lean_dec_ref(v_xImpl_2953_);
lean_dec_ref(v_indices_2952_);
lean_dec_ref(v___x_2951_);
lean_dec_ref(v_val_2950_);
lean_dec_ref(v_params_2949_);
lean_dec_ref(v_compFieldVars_2948_);
lean_dec(v_lparams_2947_);
lean_dec(v_ctors_2946_);
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
}
}
}
v___jp_2966_:
{
size_t v___x_2968_; size_t v___x_2969_; 
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_add(v_i_2958_, v___x_2968_);
v_i_2958_ = v___x_2969_;
v_b_2959_ = v_a_2967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed(lean_object** _args){
lean_object* v_ctors_3164_ = _args[0];
lean_object* v_lparams_3165_ = _args[1];
lean_object* v_compFieldVars_3166_ = _args[2];
lean_object* v_params_3167_ = _args[3];
lean_object* v_val_3168_ = _args[4];
lean_object* v___x_3169_ = _args[5];
lean_object* v_indices_3170_ = _args[6];
lean_object* v_xImpl_3171_ = _args[7];
lean_object* v___x_3172_ = _args[8];
lean_object* v_levelParams_3173_ = _args[9];
lean_object* v_as_3174_ = _args[10];
lean_object* v_sz_3175_ = _args[11];
lean_object* v_i_3176_ = _args[12];
lean_object* v_b_3177_ = _args[13];
lean_object* v___y_3178_ = _args[14];
lean_object* v___y_3179_ = _args[15];
lean_object* v___y_3180_ = _args[16];
lean_object* v___y_3181_ = _args[17];
lean_object* v___y_3182_ = _args[18];
lean_object* v___y_3183_ = _args[19];
_start:
{
size_t v_sz_boxed_3184_; size_t v_i_boxed_3185_; lean_object* v_res_3186_; 
v_sz_boxed_3184_ = lean_unbox_usize(v_sz_3175_);
lean_dec(v_sz_3175_);
v_i_boxed_3185_ = lean_unbox_usize(v_i_3176_);
lean_dec(v_i_3176_);
v_res_3186_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3164_, v_lparams_3165_, v_compFieldVars_3166_, v_params_3167_, v_val_3168_, v___x_3169_, v_indices_3170_, v_xImpl_3171_, v___x_3172_, v_levelParams_3173_, v_as_3174_, v_sz_boxed_3184_, v_i_boxed_3185_, v_b_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
lean_dec(v___y_3180_);
lean_dec_ref(v___y_3179_);
lean_dec_ref(v___y_3178_);
lean_dec_ref(v_as_3174_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(lean_object* v_lparams_3187_, lean_object* v_compFieldVars_3188_, lean_object* v_params_3189_, lean_object* v_ctors_3190_, lean_object* v_val_3191_, lean_object* v___x_3192_, lean_object* v_indices_3193_, lean_object* v_xImpl_3194_, lean_object* v___x_3195_, lean_object* v_levelParams_3196_, lean_object* v_as_3197_, size_t v_sz_3198_, size_t v_i_3199_, lean_object* v_b_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_a_3208_; uint8_t v___x_3212_; 
v___x_3212_ = lean_usize_dec_lt(v_i_3199_, v_sz_3198_);
if (v___x_3212_ == 0)
{
lean_object* v___x_3213_; 
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v_b_3200_);
return v___x_3213_;
}
else
{
lean_object* v_array_3214_; lean_object* v_start_3215_; lean_object* v_stop_3216_; uint8_t v___x_3217_; 
v_array_3214_ = lean_ctor_get(v_b_3200_, 0);
v_start_3215_ = lean_ctor_get(v_b_3200_, 1);
v_stop_3216_ = lean_ctor_get(v_b_3200_, 2);
v___x_3217_ = lean_nat_dec_lt(v_start_3215_, v_stop_3216_);
if (v___x_3217_ == 0)
{
lean_object* v___x_3218_; 
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v___x_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3218_, 0, v_b_3200_);
return v___x_3218_;
}
else
{
lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3401_; 
lean_inc(v_stop_3216_);
lean_inc(v_start_3215_);
lean_inc_ref(v_array_3214_);
v_isSharedCheck_3401_ = !lean_is_exclusive(v_b_3200_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; lean_object* v_unused_3403_; lean_object* v_unused_3404_; 
v_unused_3402_ = lean_ctor_get(v_b_3200_, 2);
lean_dec(v_unused_3402_);
v_unused_3403_ = lean_ctor_get(v_b_3200_, 1);
lean_dec(v_unused_3403_);
v_unused_3404_ = lean_ctor_get(v_b_3200_, 0);
lean_dec(v_unused_3404_);
v___x_3220_ = v_b_3200_;
v_isShared_3221_ = v_isSharedCheck_3401_;
goto v_resetjp_3219_;
}
else
{
lean_dec(v_b_3200_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3401_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3222_; lean_object* v_env_3223_; lean_object* v___x_3224_; lean_object* v_a_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3222_ = lean_st_ref_get(v___y_3205_);
v_env_3223_ = lean_ctor_get(v___x_3222_, 0);
lean_inc_ref(v_env_3223_);
lean_dec(v___x_3222_);
v___x_3224_ = lean_array_fget(v_array_3214_, v_start_3215_);
v_a_3225_ = lean_array_uget_borrowed(v_as_3197_, v_i_3199_);
v___x_3226_ = lean_unsigned_to_nat(1u);
v___x_3227_ = lean_nat_add(v_start_3215_, v___x_3226_);
lean_dec(v_start_3215_);
if (v_isShared_3221_ == 0)
{
lean_ctor_set(v___x_3220_, 1, v___x_3227_);
v___x_3229_ = v___x_3220_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_array_3214_);
lean_ctor_set(v_reuseFailAlloc_3400_, 1, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3400_, 2, v_stop_3216_);
v___x_3229_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
uint8_t v___x_3230_; 
lean_inc(v_a_3225_);
v___x_3230_ = l_Lean_isExtern(v_env_3223_, v_a_3225_);
if (v___x_3230_ == 0)
{
lean_object* v___x_3231_; size_t v_sz_3232_; size_t v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
lean_inc(v_ctors_3190_);
v___x_3231_ = lean_array_mk(v_ctors_3190_);
v_sz_3232_ = lean_array_size(v___x_3231_);
v___x_3233_ = ((size_t)0ULL);
v___x_3234_ = lean_box(v___x_3230_);
v___x_3235_ = lean_box_usize(v_sz_3232_);
v___x_3236_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2___boxed__const__1));
lean_inc(v_a_3225_);
lean_inc_ref(v_params_3189_);
lean_inc(v___x_3224_);
lean_inc_ref(v_compFieldVars_3188_);
lean_inc(v_lparams_3187_);
v___x_3237_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__0___boxed), 15, 9);
lean_closure_set(v___x_3237_, 0, v_lparams_3187_);
lean_closure_set(v___x_3237_, 1, v_compFieldVars_3188_);
lean_closure_set(v___x_3237_, 2, v___x_3224_);
lean_closure_set(v___x_3237_, 3, v_params_3189_);
lean_closure_set(v___x_3237_, 4, v_a_3225_);
lean_closure_set(v___x_3237_, 5, v___x_3234_);
lean_closure_set(v___x_3237_, 6, v___x_3235_);
lean_closure_set(v___x_3237_, 7, v___x_3236_);
lean_closure_set(v___x_3237_, 8, v___x_3231_);
v___x_3238_ = l_Lean_withoutExporting___at___00Lean_Elab_ComputedFields_overrideConstructors_spec__1___redArg(v___x_3237_, v___x_3217_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref(v___x_3238_);
lean_inc(v___y_3205_);
lean_inc_ref(v___y_3204_);
lean_inc(v___y_3203_);
lean_inc_ref(v___y_3202_);
lean_inc(v___x_3224_);
v___x_3240_ = lean_infer_type(v___x_3224_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v___x_3245_; lean_object* v___x_3246_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref(v___x_3240_);
v___x_3242_ = lean_mk_empty_array_with_capacity(v___x_3226_);
lean_inc_ref(v_val_3191_);
lean_inc_ref(v___x_3242_);
v___x_3243_ = lean_array_push(v___x_3242_, v_val_3191_);
lean_inc_ref(v___x_3192_);
v___x_3244_ = l_Array_append___redArg(v___x_3192_, v___x_3243_);
lean_dec_ref(v___x_3243_);
v___x_3245_ = 1;
v___x_3246_ = l_Lean_Meta_mkForallFVars(v___x_3244_, v_a_3241_, v___x_3230_, v___x_3217_, v___x_3217_, v___x_3245_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref(v___x_3246_);
lean_inc(v___y_3205_);
lean_inc_ref(v___y_3204_);
lean_inc(v___y_3203_);
lean_inc_ref(v___y_3202_);
v___x_3248_ = lean_infer_type(v___x_3224_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref(v___x_3248_);
lean_inc_ref(v_xImpl_3194_);
lean_inc_ref(v_indices_3193_);
v___x_3250_ = lean_array_push(v_indices_3193_, v_xImpl_3194_);
v___x_3251_ = l_Lean_Meta_mkLambdaFVars(v___x_3250_, v_a_3249_, v___x_3230_, v___x_3217_, v___x_3230_, v___x_3217_, v___x_3245_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec_ref(v___x_3250_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_object* v_a_3252_; lean_object* v___x_3253_; 
v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_a_3252_);
lean_dec_ref(v___x_3251_);
lean_inc(v___y_3205_);
lean_inc_ref(v___y_3204_);
lean_inc(v___y_3203_);
lean_inc_ref(v___y_3202_);
lean_inc_ref(v_xImpl_3194_);
v___x_3253_ = lean_infer_type(v_xImpl_3194_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v___x_3255_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___x_3253_);
lean_inc_ref(v_val_3191_);
v___x_3255_ = l_Lean_Elab_ComputedFields_mkUnsafeCastTo(v_a_3254_, v_val_3191_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3255_) == 0)
{
lean_object* v_a_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; size_t v_sz_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v_a_3256_ = lean_ctor_get(v___x_3255_, 0);
lean_inc(v_a_3256_);
lean_dec_ref(v___x_3255_);
lean_inc(v___x_3195_);
v___x_3257_ = l_Lean_mkCasesOnName(v___x_3195_);
lean_inc_ref(v___x_3242_);
v___x_3258_ = lean_array_push(v___x_3242_, v_a_3252_);
lean_inc_ref(v_params_3189_);
v___x_3259_ = l_Array_append___redArg(v_params_3189_, v___x_3258_);
lean_dec_ref(v___x_3258_);
v___x_3260_ = l_Array_append___redArg(v___x_3259_, v_indices_3193_);
v___x_3261_ = lean_array_push(v___x_3242_, v_a_3256_);
v___x_3262_ = l_Array_append___redArg(v___x_3260_, v___x_3261_);
lean_dec_ref(v___x_3261_);
v___x_3263_ = l_Array_append___redArg(v___x_3262_, v_a_3239_);
lean_dec(v_a_3239_);
v_sz_3264_ = lean_array_size(v___x_3263_);
v___x_3265_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__1(v_sz_3264_, v___x_3233_, v___x_3263_);
v___x_3266_ = l_Lean_Meta_mkAppOptM(v___x_3257_, v___x_3265_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref(v___x_3266_);
v___x_3268_ = l_Lean_Meta_mkLambdaFVars(v___x_3244_, v_a_3267_, v___x_3230_, v___x_3217_, v___x_3230_, v___x_3217_, v___x_3245_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec_ref(v___x_3244_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___y_3273_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_3225_);
v___x_3271_ = l_Lean_Name_append(v_a_3225_, v___x_3270_);
lean_inc(v_levelParams_3196_);
lean_inc(v___x_3271_);
v___x_3287_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3271_);
lean_ctor_set(v___x_3287_, 1, v_levelParams_3196_);
lean_ctor_set(v___x_3287_, 2, v_a_3247_);
v___x_3288_ = lean_box(0);
v___x_3289_ = 0;
v___x_3290_ = lean_box(0);
lean_inc(v___x_3271_);
v___x_3291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3271_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_3292_, 0, v___x_3287_);
lean_ctor_set(v___x_3292_, 1, v_a_3269_);
lean_ctor_set(v___x_3292_, 2, v___x_3288_);
lean_ctor_set(v___x_3292_, 3, v___x_3291_);
lean_ctor_set_uint8(v___x_3292_, sizeof(void*)*4, v___x_3289_);
v___x_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3292_);
v___x_3294_ = l_Lean_addDecl(v___x_3293_, v___x_3230_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v___x_3295_; lean_object* v_env_3296_; lean_object* v___x_3297_; 
lean_dec_ref(v___x_3294_);
v___x_3295_ = lean_st_ref_get(v___y_3205_);
v_env_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc_ref(v_env_3296_);
lean_dec(v___x_3295_);
lean_inc(v_a_3225_);
v___x_3297_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_3296_, v_a_3225_);
if (lean_obj_tag(v___x_3297_) == 1)
{
lean_object* v_val_3298_; uint8_t v___x_3299_; lean_object* v___x_3300_; 
v_val_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_val_3298_);
lean_dec_ref(v___x_3297_);
v___x_3299_ = lean_unbox(v_val_3298_);
lean_dec(v_val_3298_);
lean_inc(v___x_3271_);
v___x_3300_ = l_Lean_Meta_setInlineAttribute(v___x_3271_, v___x_3299_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_dec_ref(v___x_3300_);
v___y_3273_ = v___y_3201_;
v___y_3274_ = v___y_3202_;
v___y_3275_ = v___y_3203_;
v___y_3276_ = v___y_3204_;
v___y_3277_ = v___y_3205_;
goto v___jp_3272_;
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec(v___x_3271_);
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
else
{
lean_dec(v___x_3297_);
v___y_3273_ = v___y_3201_;
v___y_3274_ = v___y_3202_;
v___y_3275_ = v___y_3203_;
v___y_3276_ = v___y_3204_;
v___y_3277_ = v___y_3205_;
goto v___jp_3272_;
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec(v___x_3271_);
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3309_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3294_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3294_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
v___jp_3272_:
{
lean_object* v___x_3278_; 
lean_inc(v_a_3225_);
v___x_3278_ = l_Lean_setImplementedBy___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__6(v_a_3225_, v___x_3271_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_dec_ref(v___x_3278_);
v_a_3208_ = v___x_3229_;
goto v___jp_3207_;
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3279_ = lean_ctor_get(v___x_3278_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3278_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3278_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3278_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3317_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3268_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3268_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3325_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3266_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3266_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec(v_a_3252_);
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3242_);
lean_dec(v_a_3239_);
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3333_ = lean_ctor_get(v___x_3255_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3255_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3255_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3255_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
else
{
lean_object* v_a_3341_; lean_object* v___x_3343_; uint8_t v_isShared_3344_; uint8_t v_isSharedCheck_3348_; 
lean_dec(v_a_3252_);
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3242_);
lean_dec(v_a_3239_);
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3341_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3348_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3348_ == 0)
{
v___x_3343_ = v___x_3253_;
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
else
{
lean_inc(v_a_3341_);
lean_dec(v___x_3253_);
v___x_3343_ = lean_box(0);
v_isShared_3344_ = v_isSharedCheck_3348_;
goto v_resetjp_3342_;
}
v_resetjp_3342_:
{
lean_object* v___x_3346_; 
if (v_isShared_3344_ == 0)
{
v___x_3346_ = v___x_3343_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
}
}
else
{
lean_object* v_a_3349_; lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3242_);
lean_dec(v_a_3239_);
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3349_ = lean_ctor_get(v___x_3251_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3251_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3351_ = v___x_3251_;
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
else
{
lean_inc(v_a_3349_);
lean_dec(v___x_3251_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3356_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3354_; 
if (v_isShared_3352_ == 0)
{
v___x_3354_ = v___x_3351_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v_a_3247_);
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3242_);
lean_dec(v_a_3239_);
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3357_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3248_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3248_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec_ref(v___x_3244_);
lean_dec_ref(v___x_3242_);
lean_dec(v_a_3239_);
lean_dec_ref(v___x_3229_);
lean_dec(v___x_3224_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3365_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3246_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3246_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v_a_3239_);
lean_dec_ref(v___x_3229_);
lean_dec(v___x_3224_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3373_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3240_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3240_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
lean_dec_ref(v___x_3229_);
lean_dec(v___x_3224_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3381_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3238_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3238_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
else
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
lean_dec(v___x_3224_);
v___x_3389_ = lean_mk_empty_array_with_capacity(v___x_3226_);
lean_inc(v_a_3225_);
v___x_3390_ = lean_array_push(v___x_3389_, v_a_3225_);
v___x_3391_ = l_Lean_compileDecls(v___x_3390_, v___x_3217_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3391_) == 0)
{
lean_dec_ref(v___x_3391_);
v_a_3208_ = v___x_3229_;
goto v___jp_3207_;
}
else
{
lean_object* v_a_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
lean_dec_ref(v___x_3229_);
lean_dec(v_levelParams_3196_);
lean_dec(v___x_3195_);
lean_dec_ref(v_xImpl_3194_);
lean_dec_ref(v_indices_3193_);
lean_dec_ref(v___x_3192_);
lean_dec_ref(v_val_3191_);
lean_dec(v_ctors_3190_);
lean_dec_ref(v_params_3189_);
lean_dec_ref(v_compFieldVars_3188_);
lean_dec(v_lparams_3187_);
v_a_3392_ = lean_ctor_get(v___x_3391_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3391_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3394_ = v___x_3391_;
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
else
{
lean_inc(v_a_3392_);
lean_dec(v___x_3391_);
v___x_3394_ = lean_box(0);
v_isShared_3395_ = v_isSharedCheck_3399_;
goto v_resetjp_3393_;
}
v_resetjp_3393_:
{
lean_object* v___x_3397_; 
if (v_isShared_3395_ == 0)
{
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v_a_3392_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
}
}
}
}
}
v___jp_3207_:
{
size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; 
v___x_3209_ = ((size_t)1ULL);
v___x_3210_ = lean_usize_add(v_i_3199_, v___x_3209_);
v___x_3211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2_spec__2(v_ctors_3190_, v_lparams_3187_, v_compFieldVars_3188_, v_params_3189_, v_val_3191_, v___x_3192_, v_indices_3193_, v_xImpl_3194_, v___x_3195_, v_levelParams_3196_, v_as_3197_, v_sz_3198_, v___x_3210_, v_a_3208_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
return v___x_3211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2___boxed(lean_object** _args){
lean_object* v_lparams_3405_ = _args[0];
lean_object* v_compFieldVars_3406_ = _args[1];
lean_object* v_params_3407_ = _args[2];
lean_object* v_ctors_3408_ = _args[3];
lean_object* v_val_3409_ = _args[4];
lean_object* v___x_3410_ = _args[5];
lean_object* v_indices_3411_ = _args[6];
lean_object* v_xImpl_3412_ = _args[7];
lean_object* v___x_3413_ = _args[8];
lean_object* v_levelParams_3414_ = _args[9];
lean_object* v_as_3415_ = _args[10];
lean_object* v_sz_3416_ = _args[11];
lean_object* v_i_3417_ = _args[12];
lean_object* v_b_3418_ = _args[13];
lean_object* v___y_3419_ = _args[14];
lean_object* v___y_3420_ = _args[15];
lean_object* v___y_3421_ = _args[16];
lean_object* v___y_3422_ = _args[17];
lean_object* v___y_3423_ = _args[18];
lean_object* v___y_3424_ = _args[19];
_start:
{
size_t v_sz_boxed_3425_; size_t v_i_boxed_3426_; lean_object* v_res_3427_; 
v_sz_boxed_3425_ = lean_unbox_usize(v_sz_3416_);
lean_dec(v_sz_3416_);
v_i_boxed_3426_ = lean_unbox_usize(v_i_3417_);
lean_dec(v_i_3417_);
v_res_3427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3405_, v_compFieldVars_3406_, v_params_3407_, v_ctors_3408_, v_val_3409_, v___x_3410_, v_indices_3411_, v_xImpl_3412_, v___x_3413_, v_levelParams_3414_, v_as_3415_, v_sz_boxed_3425_, v_i_boxed_3426_, v_b_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v_as_3415_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(lean_object* v_compFieldVars_3428_, lean_object* v_compFields_3429_, lean_object* v_lparams_3430_, lean_object* v_params_3431_, lean_object* v_ctors_3432_, lean_object* v_val_3433_, lean_object* v___x_3434_, lean_object* v_indices_3435_, lean_object* v___x_3436_, lean_object* v_levelParams_3437_, lean_object* v_xImpl_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; size_t v_sz_3448_; size_t v___x_3449_; lean_object* v___x_3450_; 
v___x_3445_ = lean_unsigned_to_nat(0u);
v___x_3446_ = lean_array_get_size(v_compFieldVars_3428_);
lean_inc_ref(v_compFieldVars_3428_);
v___x_3447_ = l_Array_toSubarray___redArg(v_compFieldVars_3428_, v___x_3445_, v___x_3446_);
v_sz_3448_ = lean_array_size(v_compFields_3429_);
v___x_3449_ = ((size_t)0ULL);
v___x_3450_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_overrideComputedFields_spec__2(v_lparams_3430_, v_compFieldVars_3428_, v_params_3431_, v_ctors_3432_, v_val_3433_, v___x_3434_, v_indices_3435_, v_xImpl_3438_, v___x_3436_, v_levelParams_3437_, v_compFields_3429_, v_sz_3448_, v___x_3449_, v___x_3447_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3458_; 
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3458_ == 0)
{
lean_object* v_unused_3459_; 
v_unused_3459_ = lean_ctor_get(v___x_3450_, 0);
lean_dec(v_unused_3459_);
v___x_3452_ = v___x_3450_;
v_isShared_3453_ = v_isSharedCheck_3458_;
goto v_resetjp_3451_;
}
else
{
lean_dec(v___x_3450_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3458_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3454_; lean_object* v___x_3456_; 
v___x_3454_ = lean_box(0);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3454_);
v___x_3456_ = v___x_3452_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v___x_3454_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
else
{
lean_object* v_a_3460_; lean_object* v___x_3462_; uint8_t v_isShared_3463_; uint8_t v_isSharedCheck_3467_; 
v_a_3460_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3467_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3467_ == 0)
{
v___x_3462_ = v___x_3450_;
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
else
{
lean_inc(v_a_3460_);
lean_dec(v___x_3450_);
v___x_3462_ = lean_box(0);
v_isShared_3463_ = v_isSharedCheck_3467_;
goto v_resetjp_3461_;
}
v_resetjp_3461_:
{
lean_object* v___x_3465_; 
if (v_isShared_3463_ == 0)
{
v___x_3465_ = v___x_3462_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v_a_3460_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed(lean_object** _args){
lean_object* v_compFieldVars_3468_ = _args[0];
lean_object* v_compFields_3469_ = _args[1];
lean_object* v_lparams_3470_ = _args[2];
lean_object* v_params_3471_ = _args[3];
lean_object* v_ctors_3472_ = _args[4];
lean_object* v_val_3473_ = _args[5];
lean_object* v___x_3474_ = _args[6];
lean_object* v_indices_3475_ = _args[7];
lean_object* v___x_3476_ = _args[8];
lean_object* v_levelParams_3477_ = _args[9];
lean_object* v_xImpl_3478_ = _args[10];
lean_object* v___y_3479_ = _args[11];
lean_object* v___y_3480_ = _args[12];
lean_object* v___y_3481_ = _args[13];
lean_object* v___y_3482_ = _args[14];
lean_object* v___y_3483_ = _args[15];
lean_object* v___y_3484_ = _args[16];
_start:
{
lean_object* v_res_3485_; 
v_res_3485_ = l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0(v_compFieldVars_3468_, v_compFields_3469_, v_lparams_3470_, v_params_3471_, v_ctors_3472_, v_val_3473_, v___x_3474_, v_indices_3475_, v___x_3476_, v_levelParams_3477_, v_xImpl_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_, v___y_3483_);
lean_dec(v___y_3483_);
lean_dec_ref(v___y_3482_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec_ref(v_compFields_3469_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields(lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v_toInductiveVal_3495_; lean_object* v_toConstantVal_3496_; lean_object* v_lparams_3497_; lean_object* v_params_3498_; lean_object* v_compFields_3499_; lean_object* v_compFieldVars_3500_; lean_object* v_indices_3501_; lean_object* v_val_3502_; lean_object* v_ctors_3503_; lean_object* v_name_3504_; lean_object* v_levelParams_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___f_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_toInductiveVal_3495_ = lean_ctor_get(v_a_3489_, 0);
v_toConstantVal_3496_ = lean_ctor_get(v_toInductiveVal_3495_, 0);
v_lparams_3497_ = lean_ctor_get(v_a_3489_, 1);
v_params_3498_ = lean_ctor_get(v_a_3489_, 2);
v_compFields_3499_ = lean_ctor_get(v_a_3489_, 3);
v_compFieldVars_3500_ = lean_ctor_get(v_a_3489_, 4);
v_indices_3501_ = lean_ctor_get(v_a_3489_, 5);
v_val_3502_ = lean_ctor_get(v_a_3489_, 6);
v_ctors_3503_ = lean_ctor_get(v_toInductiveVal_3495_, 4);
v_name_3504_ = lean_ctor_get(v_toConstantVal_3496_, 0);
v_levelParams_3505_ = lean_ctor_get(v_toConstantVal_3496_, 1);
v___x_3506_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_3507_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__1));
lean_inc(v_name_3504_);
v___x_3508_ = l_Lean_Name_append(v_name_3504_, v___x_3507_);
lean_inc(v_lparams_3497_);
lean_inc(v___x_3508_);
v___x_3509_ = l_Lean_mkConst(v___x_3508_, v_lparams_3497_);
lean_inc_ref(v_params_3498_);
v___x_3510_ = l_Array_append___redArg(v_params_3498_, v_indices_3501_);
lean_inc(v_levelParams_3505_);
lean_inc_ref(v_indices_3501_);
lean_inc_ref(v___x_3510_);
lean_inc_ref(v_val_3502_);
lean_inc(v_ctors_3503_);
lean_inc_ref(v_params_3498_);
lean_inc(v_lparams_3497_);
lean_inc_ref(v_compFields_3499_);
lean_inc_ref(v_compFieldVars_3500_);
v___f_3511_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_overrideComputedFields___lam__0___boxed), 17, 10);
lean_closure_set(v___f_3511_, 0, v_compFieldVars_3500_);
lean_closure_set(v___f_3511_, 1, v_compFields_3499_);
lean_closure_set(v___f_3511_, 2, v_lparams_3497_);
lean_closure_set(v___f_3511_, 3, v_params_3498_);
lean_closure_set(v___f_3511_, 4, v_ctors_3503_);
lean_closure_set(v___f_3511_, 5, v_val_3502_);
lean_closure_set(v___f_3511_, 6, v___x_3510_);
lean_closure_set(v___f_3511_, 7, v_indices_3501_);
lean_closure_set(v___f_3511_, 8, v___x_3508_);
lean_closure_set(v___f_3511_, 9, v_levelParams_3505_);
v___x_3512_ = l_Lean_mkAppN(v___x_3509_, v___x_3510_);
lean_dec_ref(v___x_3510_);
v___x_3513_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__3___redArg(v___x_3506_, v___x_3512_, v___f_3511_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_);
lean_dec_ref(v_a_3489_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_overrideComputedFields___boxed(lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(lean_object* v_k_3521_, lean_object* v_b_3522_, lean_object* v_c_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_){
_start:
{
lean_object* v___x_3529_; 
lean_inc(v___y_3527_);
lean_inc_ref(v___y_3526_);
lean_inc(v___y_3525_);
lean_inc_ref(v___y_3524_);
v___x_3529_ = lean_apply_7(v_k_3521_, v_b_3522_, v_c_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, lean_box(0));
return v___x_3529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed(lean_object* v_k_3530_, lean_object* v_b_3531_, lean_object* v_c_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
lean_object* v_res_3538_; 
v_res_3538_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0(v_k_3530_, v_b_3531_, v_c_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_);
lean_dec(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(lean_object* v_type_3539_, lean_object* v_k_3540_, uint8_t v_cleanupAnnotations_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v___f_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___f_3547_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3547_, 0, v_k_3540_);
v___x_3548_ = 0;
v___x_3549_ = lean_box(0);
v___x_3550_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3548_, v___x_3549_, v_type_3539_, v___f_3547_, v_cleanupAnnotations_3541_, v___x_3548_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
v_a_3559_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3550_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3550_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg___boxed(lean_object* v_type_3567_, lean_object* v_k_3568_, lean_object* v_cleanupAnnotations_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3575_; lean_object* v_res_3576_; 
v_cleanupAnnotations_boxed_3575_ = lean_unbox(v_cleanupAnnotations_3569_);
v_res_3576_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3567_, v_k_3568_, v_cleanupAnnotations_boxed_3575_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
return v_res_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(lean_object* v_00_u03b1_3577_, lean_object* v_type_3578_, lean_object* v_k_3579_, uint8_t v_cleanupAnnotations_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_3578_, v_k_3579_, v_cleanupAnnotations_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___boxed(lean_object* v_00_u03b1_3587_, lean_object* v_type_3588_, lean_object* v_k_3589_, lean_object* v_cleanupAnnotations_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3596_; lean_object* v_res_3597_; 
v_cleanupAnnotations_boxed_3596_ = lean_unbox(v_cleanupAnnotations_3590_);
v_res_3597_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3(v_00_u03b1_3587_, v_type_3588_, v_k_3589_, v_cleanupAnnotations_boxed_3596_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(lean_object* v_a_3598_, lean_object* v___x_3599_, lean_object* v___x_3600_, lean_object* v_compFields_3601_, lean_object* v___x_3602_, lean_object* v_val_3603_, lean_object* v_compFieldVars_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3610_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_3610_, 0, v_a_3598_);
lean_ctor_set(v___x_3610_, 1, v___x_3599_);
lean_ctor_set(v___x_3610_, 2, v___x_3600_);
lean_ctor_set(v___x_3610_, 3, v_compFields_3601_);
lean_ctor_set(v___x_3610_, 4, v_compFieldVars_3604_);
lean_ctor_set(v___x_3610_, 5, v___x_3602_);
lean_ctor_set(v___x_3610_, 6, v_val_3603_);
v___x_3611_ = l_Lean_Elab_ComputedFields_validateComputedFields(v___x_3610_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v___x_3612_; 
lean_dec_ref(v___x_3611_);
lean_inc_ref(v___x_3610_);
v___x_3612_ = l_Lean_Elab_ComputedFields_mkImplType(v___x_3610_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v___x_3613_; 
lean_dec_ref(v___x_3612_);
lean_inc_ref(v___x_3610_);
v___x_3613_ = l_Lean_Elab_ComputedFields_overrideCasesOn(v___x_3610_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v___x_3614_; 
lean_dec_ref(v___x_3613_);
lean_inc_ref(v___x_3610_);
v___x_3614_ = l_Lean_Elab_ComputedFields_overrideConstructors(v___x_3610_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v___x_3615_; 
lean_dec_ref(v___x_3614_);
v___x_3615_ = l_Lean_Elab_ComputedFields_overrideComputedFields(v___x_3610_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_);
return v___x_3615_;
}
else
{
lean_dec_ref(v___x_3610_);
return v___x_3614_;
}
}
else
{
lean_dec_ref(v___x_3610_);
return v___x_3613_;
}
}
else
{
lean_dec_ref(v___x_3610_);
return v___x_3612_;
}
}
else
{
lean_dec_ref(v___x_3610_);
return v___x_3611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed(lean_object* v_a_3616_, lean_object* v___x_3617_, lean_object* v___x_3618_, lean_object* v_compFields_3619_, lean_object* v___x_3620_, lean_object* v_val_3621_, lean_object* v_compFieldVars_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v_res_3628_; 
v_res_3628_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0(v_a_3616_, v___x_3617_, v___x_3618_, v_compFields_3619_, v___x_3620_, v_val_3621_, v_compFieldVars_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_);
lean_dec(v___y_3626_);
lean_dec_ref(v___y_3625_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(lean_object* v___x_3629_, lean_object* v___x_3630_, lean_object* v_val_3631_, lean_object* v_v_3632_, lean_object* v_x_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3639_ = l_Array_append___redArg(v___x_3629_, v___x_3630_);
v___x_3640_ = lean_unsigned_to_nat(1u);
v___x_3641_ = lean_mk_empty_array_with_capacity(v___x_3640_);
v___x_3642_ = lean_array_push(v___x_3641_, v_val_3631_);
v___x_3643_ = l_Array_append___redArg(v___x_3639_, v___x_3642_);
lean_dec_ref(v___x_3642_);
v___x_3644_ = l_Lean_Meta_mkAppM(v_v_3632_, v___x_3643_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3644_);
lean_inc(v___y_3637_);
lean_inc_ref(v___y_3636_);
lean_inc(v___y_3635_);
lean_inc_ref(v___y_3634_);
v___x_3646_ = lean_infer_type(v_a_3645_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3646_;
}
else
{
return v___x_3644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed(lean_object* v___x_3647_, lean_object* v___x_3648_, lean_object* v_val_3649_, lean_object* v_v_3650_, lean_object* v_x_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0(v___x_3647_, v___x_3648_, v_val_3649_, v_v_3650_, v_x_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec_ref(v_x_3651_);
lean_dec_ref(v___x_3648_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(lean_object* v___x_3658_, lean_object* v___x_3659_, lean_object* v_val_3660_, size_t v_sz_3661_, size_t v_i_3662_, lean_object* v_bs_3663_){
_start:
{
uint8_t v___x_3664_; 
v___x_3664_ = lean_usize_dec_lt(v_i_3662_, v_sz_3661_);
if (v___x_3664_ == 0)
{
lean_dec_ref(v_val_3660_);
lean_dec_ref(v___x_3659_);
lean_dec_ref(v___x_3658_);
return v_bs_3663_;
}
else
{
lean_object* v_v_3665_; lean_object* v___f_3666_; lean_object* v___x_3667_; lean_object* v_bs_x27_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; size_t v___x_3672_; size_t v___x_3673_; lean_object* v___x_3674_; 
v_v_3665_ = lean_array_uget(v_bs_3663_, v_i_3662_);
lean_inc(v_v_3665_);
lean_inc_ref(v_val_3660_);
lean_inc_ref(v___x_3659_);
lean_inc_ref(v___x_3658_);
v___f_3666_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___lam__0___boxed), 10, 4);
lean_closure_set(v___f_3666_, 0, v___x_3658_);
lean_closure_set(v___f_3666_, 1, v___x_3659_);
lean_closure_set(v___f_3666_, 2, v_val_3660_);
lean_closure_set(v___f_3666_, 3, v_v_3665_);
v___x_3667_ = lean_unsigned_to_nat(0u);
v_bs_x27_3668_ = lean_array_uset(v_bs_3663_, v_i_3662_, v___x_3667_);
v___x_3669_ = lean_box(0);
v___x_3670_ = l_Lean_Name_updatePrefix(v_v_3665_, v___x_3669_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v___x_3670_);
lean_ctor_set(v___x_3671_, 1, v___f_3666_);
v___x_3672_ = ((size_t)1ULL);
v___x_3673_ = lean_usize_add(v_i_3662_, v___x_3672_);
v___x_3674_ = lean_array_uset(v_bs_x27_3668_, v_i_3662_, v___x_3671_);
v_i_3662_ = v___x_3673_;
v_bs_3663_ = v___x_3674_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0___boxed(lean_object* v___x_3676_, lean_object* v___x_3677_, lean_object* v_val_3678_, lean_object* v_sz_3679_, lean_object* v_i_3680_, lean_object* v_bs_3681_){
_start:
{
size_t v_sz_boxed_3682_; size_t v_i_boxed_3683_; lean_object* v_res_3684_; 
v_sz_boxed_3682_ = lean_unbox_usize(v_sz_3679_);
lean_dec(v_sz_3679_);
v_i_boxed_3683_ = lean_unbox_usize(v_i_3680_);
lean_dec(v_i_3680_);
v_res_3684_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3676_, v___x_3677_, v_val_3678_, v_sz_boxed_3682_, v_i_boxed_3683_, v_bs_3681_);
return v_res_3684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0(lean_object* v___x_3685_, lean_object* v_a_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3037__overap_3693_; lean_object* v___x_3694_; 
v___x_3692_ = l_Lean_instInhabitedExpr;
v___x_3037__overap_3693_ = l_instInhabitedOfMonad___redArg(v___x_3685_, v___x_3692_);
lean_inc(v___y_3690_);
lean_inc_ref(v___y_3689_);
lean_inc(v___y_3688_);
lean_inc_ref(v___y_3687_);
v___x_3694_ = lean_apply_5(v___x_3037__overap_3693_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, lean_box(0));
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v___x_3695_, lean_object* v_a_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0(v___x_3695_, v_a_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec(v___y_3698_);
lean_dec_ref(v___y_3697_);
lean_dec_ref(v_a_3696_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0___boxed(lean_object* v_acc_3703_, lean_object* v_declInfos_3704_, lean_object* v_k_3705_, lean_object* v_kind_3706_, lean_object* v_inst_3707_, lean_object* v_b_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
uint8_t v_kind_boxed_3714_; lean_object* v_res_3715_; 
v_kind_boxed_3714_ = lean_unbox(v_kind_3706_);
v_res_3715_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0(v_acc_3703_, v_declInfos_3704_, v_k_3705_, v_kind_boxed_3714_, v_inst_3707_, v_b_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
lean_dec_ref(v___y_3709_);
return v_res_3715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(lean_object* v_acc_3716_, lean_object* v_declInfos_3717_, lean_object* v_k_3718_, uint8_t v_kind_3719_, lean_object* v_inst_3720_, lean_object* v_name_3721_, uint8_t v_bi_3722_, lean_object* v_type_3723_, uint8_t v_kind_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_){
_start:
{
lean_object* v___x_3730_; lean_object* v___f_3731_; lean_object* v___x_3732_; 
v___x_3730_ = lean_box(v_kind_3719_);
v___f_3731_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_3731_, 0, v_acc_3716_);
lean_closure_set(v___f_3731_, 1, v_declInfos_3717_);
lean_closure_set(v___f_3731_, 2, v_k_3718_);
lean_closure_set(v___f_3731_, 3, v___x_3730_);
lean_closure_set(v___f_3731_, 4, v_inst_3720_);
v___x_3732_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3721_, v_bi_3722_, v_type_3723_, v___f_3731_, v_kind_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v_a_3741_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3732_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3732_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(lean_object* v_declInfos_3749_, lean_object* v_k_3750_, uint8_t v_kind_3751_, lean_object* v_inst_3752_, lean_object* v_acc_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
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
v___x_3809_ = lean_array_get_size(v_declInfos_3749_);
v___x_3810_ = lean_nat_dec_lt(v___x_3808_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_object* v___x_3811_; 
lean_dec_ref(v___x_3807_);
lean_dec(v_inst_3752_);
lean_dec_ref(v_declInfos_3749_);
lean_inc(v___y_3757_);
lean_inc_ref(v___y_3756_);
lean_inc(v___y_3755_);
lean_inc_ref(v___y_3754_);
v___x_3811_ = lean_apply_6(v_k_3750_, v_acc_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, lean_box(0));
return v___x_3811_;
}
else
{
lean_object* v___f_3812_; lean_object* v___x_3813_; uint8_t v___x_3814_; lean_object* v___f_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v_snd_3820_; lean_object* v_fst_3821_; lean_object* v_fst_3822_; lean_object* v_snd_3823_; lean_object* v___x_3824_; 
v___f_3812_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
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
v___x_3819_ = lean_array_get_borrowed(v___x_3818_, v_declInfos_3749_, v___x_3808_);
v_snd_3820_ = lean_ctor_get(v___x_3819_, 1);
v_fst_3821_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_fst_3821_);
v_fst_3822_ = lean_ctor_get(v_snd_3820_, 0);
v_snd_3823_ = lean_ctor_get(v_snd_3820_, 1);
lean_inc(v_snd_3823_);
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
v___x_3827_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(v_acc_3753_, v_declInfos_3749_, v_k_3750_, v_kind_3751_, v_inst_3752_, v_fst_3821_, v___x_3826_, v_a_3825_, v_kind_3751_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
return v___x_3827_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v_fst_3821_);
lean_dec_ref(v_acc_3753_);
lean_dec(v_inst_3752_);
lean_dec_ref(v_k_3750_);
lean_dec_ref(v_declInfos_3749_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___lam__0(lean_object* v_acc_3848_, lean_object* v_declInfos_3849_, lean_object* v_k_3850_, uint8_t v_kind_3851_, lean_object* v_inst_3852_, lean_object* v_b_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_array_push(v_acc_3848_, v_b_3853_);
v___x_3860_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(v_declInfos_3849_, v_k_3850_, v_kind_3851_, v_inst_3852_, v___x_3859_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg___boxed(lean_object* v_acc_3861_, lean_object* v_declInfos_3862_, lean_object* v_k_3863_, lean_object* v_kind_3864_, lean_object* v_inst_3865_, lean_object* v_name_3866_, lean_object* v_bi_3867_, lean_object* v_type_3868_, lean_object* v_kind_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
uint8_t v_kind_boxed_3875_; uint8_t v_bi_boxed_3876_; uint8_t v_kind_boxed_3877_; lean_object* v_res_3878_; 
v_kind_boxed_3875_ = lean_unbox(v_kind_3864_);
v_bi_boxed_3876_ = lean_unbox(v_bi_3867_);
v_kind_boxed_3877_ = lean_unbox(v_kind_3869_);
v_res_3878_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(v_acc_3861_, v_declInfos_3862_, v_k_3863_, v_kind_boxed_3875_, v_inst_3865_, v_name_3866_, v_bi_boxed_3876_, v_type_3868_, v_kind_boxed_3877_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
return v_res_3878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_declInfos_3879_, lean_object* v_k_3880_, lean_object* v_kind_3881_, lean_object* v_inst_3882_, lean_object* v_acc_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
uint8_t v_kind_boxed_3889_; lean_object* v_res_3890_; 
v_kind_boxed_3889_ = lean_unbox(v_kind_3881_);
v_res_3890_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(v_declInfos_3879_, v_k_3880_, v_kind_boxed_3889_, v_inst_3882_, v_acc_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(lean_object* v_inst_3891_, lean_object* v_declInfos_3892_, lean_object* v_k_3893_, uint8_t v_kind_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_3901_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(v_declInfos_3892_, v_k_3893_, v_kind_3894_, v_inst_3891_, v___x_3900_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg___boxed(lean_object* v_inst_3902_, lean_object* v_declInfos_3903_, lean_object* v_k_3904_, lean_object* v_kind_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_){
_start:
{
uint8_t v_kind_boxed_3911_; lean_object* v_res_3912_; 
v_kind_boxed_3911_ = lean_unbox(v_kind_3905_);
v_res_3912_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(v_inst_3902_, v_declInfos_3903_, v_k_3904_, v_kind_boxed_3911_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(size_t v_sz_3913_, size_t v_i_3914_, lean_object* v_bs_3915_){
_start:
{
uint8_t v___x_3916_; 
v___x_3916_ = lean_usize_dec_lt(v_i_3914_, v_sz_3913_);
if (v___x_3916_ == 0)
{
return v_bs_3915_;
}
else
{
lean_object* v_v_3917_; lean_object* v_fst_3918_; lean_object* v_snd_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3935_; 
v_v_3917_ = lean_array_uget(v_bs_3915_, v_i_3914_);
v_fst_3918_ = lean_ctor_get(v_v_3917_, 0);
v_snd_3919_ = lean_ctor_get(v_v_3917_, 1);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_v_3917_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3921_ = v_v_3917_;
v_isShared_3922_ = v_isSharedCheck_3935_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_snd_3919_);
lean_inc(v_fst_3918_);
lean_dec(v_v_3917_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3935_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v_bs_x27_3924_; uint8_t v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3923_ = lean_unsigned_to_nat(0u);
v_bs_x27_3924_ = lean_array_uset(v_bs_3915_, v_i_3914_, v___x_3923_);
v___x_3925_ = 0;
v___x_3926_ = lean_box(v___x_3925_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3926_);
v___x_3928_ = v___x_3921_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3934_, 1, v_snd_3919_);
v___x_3928_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; size_t v___x_3930_; size_t v___x_3931_; lean_object* v___x_3932_; 
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v_fst_3918_);
lean_ctor_set(v___x_3929_, 1, v___x_3928_);
v___x_3930_ = ((size_t)1ULL);
v___x_3931_ = lean_usize_add(v_i_3914_, v___x_3930_);
v___x_3932_ = lean_array_uset(v_bs_x27_3924_, v_i_3914_, v___x_3929_);
v_i_3914_ = v___x_3931_;
v_bs_3915_ = v___x_3932_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1___boxed(lean_object* v_sz_3936_, lean_object* v_i_3937_, lean_object* v_bs_3938_){
_start:
{
size_t v_sz_boxed_3939_; size_t v_i_boxed_3940_; lean_object* v_res_3941_; 
v_sz_boxed_3939_ = lean_unbox_usize(v_sz_3936_);
lean_dec(v_sz_3936_);
v_i_boxed_3940_ = lean_unbox_usize(v_i_3937_);
lean_dec(v_i_3937_);
v_res_3941_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_boxed_3939_, v_i_boxed_3940_, v_bs_3938_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(lean_object* v_inst_3942_, lean_object* v_declInfos_3943_, lean_object* v_k_3944_, uint8_t v_kind_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
size_t v_sz_3951_; size_t v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_sz_3951_ = lean_array_size(v_declInfos_3943_);
v___x_3952_ = ((size_t)0ULL);
v___x_3953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__1(v_sz_3951_, v___x_3952_, v_declInfos_3943_);
v___x_3954_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(v_inst_3942_, v___x_3953_, v_k_3944_, v_kind_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg___boxed(lean_object* v_inst_3955_, lean_object* v_declInfos_3956_, lean_object* v_k_3957_, lean_object* v_kind_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_){
_start:
{
uint8_t v_kind_boxed_3964_; lean_object* v_res_3965_; 
v_kind_boxed_3964_ = lean_unbox(v_kind_3958_);
v_res_3965_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(v_inst_3955_, v_declInfos_3956_, v_k_3957_, v_kind_boxed_3964_, v___y_3959_, v___y_3960_, v___y_3961_, v___y_3962_);
lean_dec(v___y_3962_);
lean_dec_ref(v___y_3961_);
lean_dec(v___y_3960_);
lean_dec_ref(v___y_3959_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(lean_object* v_paramsIndices_3966_, lean_object* v_numParams_3967_, lean_object* v_a_3968_, lean_object* v___x_3969_, lean_object* v_compFields_3970_, lean_object* v___x_3971_, lean_object* v_val_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_){
_start:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v_lower_3983_; lean_object* v_upper_3984_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v___x_3978_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_3967_);
lean_inc_ref(v_paramsIndices_3966_);
v___x_3979_ = l_Array_toSubarray___redArg(v_paramsIndices_3966_, v___x_3978_, v_numParams_3967_);
v___x_3980_ = ((lean_object*)(l_List_mapM_loop___at___00Lean_Elab_ComputedFields_mkImplType_spec__1___lam__0___closed__2));
v___x_3981_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3979_, v___x_3980_);
v___x_3993_ = lean_array_get_size(v_paramsIndices_3966_);
v___x_3994_ = lean_nat_dec_le(v_numParams_3967_, v___x_3978_);
if (v___x_3994_ == 0)
{
v_lower_3983_ = v_numParams_3967_;
v_upper_3984_ = v___x_3993_;
goto v___jp_3982_;
}
else
{
lean_dec(v_numParams_3967_);
v_lower_3983_ = v___x_3978_;
v_upper_3984_ = v___x_3993_;
goto v___jp_3982_;
}
v___jp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___f_3987_; size_t v_sz_3988_; size_t v___x_3989_; lean_object* v___x_3990_; uint8_t v___x_3991_; lean_object* v___x_3992_; 
v___x_3985_ = l_Array_toSubarray___redArg(v_paramsIndices_3966_, v_lower_3983_, v_upper_3984_);
v___x_3986_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__1___redArg(v___x_3985_, v___x_3980_);
lean_inc_ref(v_val_3972_);
lean_inc_ref(v___x_3986_);
lean_inc_ref(v_compFields_3970_);
lean_inc_ref(v___x_3981_);
v___f_3987_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__0___boxed), 12, 6);
lean_closure_set(v___f_3987_, 0, v_a_3968_);
lean_closure_set(v___f_3987_, 1, v___x_3969_);
lean_closure_set(v___f_3987_, 2, v___x_3981_);
lean_closure_set(v___f_3987_, 3, v_compFields_3970_);
lean_closure_set(v___f_3987_, 4, v___x_3986_);
lean_closure_set(v___f_3987_, 5, v_val_3972_);
v_sz_3988_ = lean_array_size(v_compFields_3970_);
v___x_3989_ = ((size_t)0ULL);
v___x_3990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__0(v___x_3981_, v___x_3986_, v_val_3972_, v_sz_3988_, v___x_3989_, v_compFields_3970_);
v___x_3991_ = 0;
v___x_3992_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(v___x_3971_, v___x_3990_, v___f_3987_, v___x_3991_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
return v___x_3992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed(lean_object* v_paramsIndices_3995_, lean_object* v_numParams_3996_, lean_object* v_a_3997_, lean_object* v___x_3998_, lean_object* v_compFields_3999_, lean_object* v___x_4000_, lean_object* v_val_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1(v_paramsIndices_3995_, v_numParams_3996_, v_a_3997_, v___x_3998_, v_compFields_3999_, v___x_4000_, v_val_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(lean_object* v_k_4008_, lean_object* v_b_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___x_4015_; 
lean_inc(v___y_4013_);
lean_inc_ref(v___y_4012_);
lean_inc(v___y_4011_);
lean_inc_ref(v___y_4010_);
v___x_4015_ = lean_apply_6(v_k_4008_, v_b_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, lean_box(0));
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed(lean_object* v_k_4016_, lean_object* v_b_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v_res_4023_; 
v_res_4023_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0(v_k_4016_, v_b_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
return v_res_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(lean_object* v_name_4024_, uint8_t v_bi_4025_, lean_object* v_type_4026_, lean_object* v_k_4027_, uint8_t v_kind_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v___f_4034_; lean_object* v___x_4035_; 
v___f_4034_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4034_, 0, v_k_4027_);
v___x_4035_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4024_, v_bi_4025_, v_type_4026_, v___f_4034_, v_kind_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
v_a_4044_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4035_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4035_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg___boxed(lean_object* v_name_4052_, lean_object* v_bi_4053_, lean_object* v_type_4054_, lean_object* v_k_4055_, lean_object* v_kind_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
uint8_t v_bi_boxed_4062_; uint8_t v_kind_boxed_4063_; lean_object* v_res_4064_; 
v_bi_boxed_4062_ = lean_unbox(v_bi_4053_);
v_kind_boxed_4063_ = lean_unbox(v_kind_4056_);
v_res_4064_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4052_, v_bi_boxed_4062_, v_type_4054_, v_k_4055_, v_kind_boxed_4063_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(lean_object* v_name_4065_, lean_object* v_type_4066_, lean_object* v_k_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
uint8_t v___x_4073_; uint8_t v___x_4074_; lean_object* v___x_4075_; 
v___x_4073_ = 0;
v___x_4074_ = 0;
v___x_4075_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4065_, v___x_4073_, v_type_4066_, v_k_4067_, v___x_4074_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg___boxed(lean_object* v_name_4076_, lean_object* v_type_4077_, lean_object* v_k_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4076_, v_type_4077_, v_k_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(lean_object* v_numParams_4085_, lean_object* v_a_4086_, lean_object* v___x_4087_, lean_object* v_compFields_4088_, lean_object* v___x_4089_, lean_object* v_name_4090_, lean_object* v_paramsIndices_4091_, lean_object* v_x_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v___f_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_inc(v___x_4087_);
lean_inc_ref(v_paramsIndices_4091_);
v___f_4098_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__1___boxed), 12, 6);
lean_closure_set(v___f_4098_, 0, v_paramsIndices_4091_);
lean_closure_set(v___f_4098_, 1, v_numParams_4085_);
lean_closure_set(v___f_4098_, 2, v_a_4086_);
lean_closure_set(v___f_4098_, 3, v___x_4087_);
lean_closure_set(v___f_4098_, 4, v_compFields_4088_);
lean_closure_set(v___f_4098_, 5, v___x_4089_);
v___x_4099_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideComputedFields___closed__1));
v___x_4100_ = l_Lean_mkConst(v_name_4090_, v___x_4087_);
v___x_4101_ = l_Lean_mkAppN(v___x_4100_, v_paramsIndices_4091_);
lean_dec_ref(v_paramsIndices_4091_);
v___x_4102_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v___x_4099_, v___x_4101_, v___f_4098_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed(lean_object* v_numParams_4103_, lean_object* v_a_4104_, lean_object* v___x_4105_, lean_object* v_compFields_4106_, lean_object* v___x_4107_, lean_object* v_name_4108_, lean_object* v_paramsIndices_4109_, lean_object* v_x_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
lean_object* v_res_4116_; 
v_res_4116_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2(v_numParams_4103_, v_a_4104_, v___x_4105_, v_compFields_4106_, v___x_4107_, v_name_4108_, v_paramsIndices_4109_, v_x_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec_ref(v_x_4110_);
return v_res_4116_;
}
}
static lean_object* _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1(void){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = ((lean_object*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__0));
v___x_4119_ = l_Lean_stringToMessageData(v___x_4118_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(lean_object* v_declName_4120_, lean_object* v_compFields_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_declName_4120_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v_toConstantVal_4129_; lean_object* v_numParams_4130_; lean_object* v_ctors_4131_; lean_object* v___x_4132_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___x_4146_; lean_object* v___x_4147_; uint8_t v___x_4148_; 
v_a_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_a_4128_);
lean_dec_ref(v___x_4127_);
v_toConstantVal_4129_ = lean_ctor_get(v_a_4128_, 0);
v_numParams_4130_ = lean_ctor_get(v_a_4128_, 1);
lean_inc(v_numParams_4130_);
v_ctors_4131_ = lean_ctor_get(v_a_4128_, 4);
v___x_4132_ = lean_box(0);
v___x_4146_ = l_List_lengthTR___redArg(v_ctors_4131_);
v___x_4147_ = lean_unsigned_to_nat(2u);
v___x_4148_ = lean_nat_dec_lt(v___x_4146_, v___x_4147_);
lean_dec(v___x_4146_);
if (v___x_4148_ == 0)
{
v___y_4134_ = v_a_4122_;
v___y_4135_ = v_a_4123_;
v___y_4136_ = v_a_4124_;
v___y_4137_ = v_a_4125_;
goto v___jp_4133_;
}
else
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
lean_dec(v_numParams_4130_);
lean_dec(v_a_4128_);
lean_dec_ref(v_compFields_4121_);
v___x_4149_ = lean_obj_once(&l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1, &l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1_once, _init_l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___closed__1);
v___x_4150_ = l_Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1___redArg(v___x_4149_, v_a_4122_, v_a_4123_, v_a_4124_, v_a_4125_);
return v___x_4150_;
}
v___jp_4133_:
{
lean_object* v_name_4138_; lean_object* v_levelParams_4139_; lean_object* v_type_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___f_4143_; uint8_t v___x_4144_; lean_object* v___x_4145_; 
v_name_4138_ = lean_ctor_get(v_toConstantVal_4129_, 0);
lean_inc(v_name_4138_);
v_levelParams_4139_ = lean_ctor_get(v_toConstantVal_4129_, 1);
v_type_4140_ = lean_ctor_get(v_toConstantVal_4129_, 2);
lean_inc_ref(v_type_4140_);
v___x_4141_ = lean_box(0);
lean_inc(v_levelParams_4139_);
v___x_4142_ = l_List_mapTR_loop___at___00Lean_Elab_ComputedFields_overrideCasesOn_spec__5(v_levelParams_4139_, v___x_4141_);
v___f_4143_ = lean_alloc_closure((void*)(l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___lam__2___boxed), 13, 6);
lean_closure_set(v___f_4143_, 0, v_numParams_4130_);
lean_closure_set(v___f_4143_, 1, v_a_4128_);
lean_closure_set(v___f_4143_, 2, v___x_4142_);
lean_closure_set(v___f_4143_, 3, v_compFields_4121_);
lean_closure_set(v___f_4143_, 4, v___x_4132_);
lean_closure_set(v___f_4143_, 5, v_name_4138_);
v___x_4144_ = 0;
v___x_4145_ = l_Lean_Meta_forallTelescope___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__3___redArg(v_type_4140_, v___f_4143_, v___x_4144_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
return v___x_4145_;
}
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_dec_ref(v_compFields_4121_);
v_a_4151_ = lean_ctor_get(v___x_4127_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4127_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4127_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4127_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_mkComputedFieldOverrides___boxed(lean_object* v_declName_4159_, lean_object* v_compFields_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_declName_4159_, v_compFields_4160_, v_a_4161_, v_a_4162_, v_a_4163_, v_a_4164_);
lean_dec(v_a_4164_);
lean_dec_ref(v_a_4163_);
lean_dec(v_a_4162_);
lean_dec_ref(v_a_4161_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(lean_object* v_00_u03b1_4167_, lean_object* v_inst_4168_, lean_object* v_declInfos_4169_, lean_object* v_k_4170_, uint8_t v_kind_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_){
_start:
{
lean_object* v___x_4177_; 
v___x_4177_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___redArg(v_inst_4168_, v_declInfos_4169_, v_k_4170_, v_kind_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
return v___x_4177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1___boxed(lean_object* v_00_u03b1_4178_, lean_object* v_inst_4179_, lean_object* v_declInfos_4180_, lean_object* v_k_4181_, lean_object* v_kind_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
uint8_t v_kind_boxed_4188_; lean_object* v_res_4189_; 
v_kind_boxed_4188_ = lean_unbox(v_kind_4182_);
v_res_4189_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1(v_00_u03b1_4178_, v_inst_4179_, v_declInfos_4180_, v_k_4181_, v_kind_boxed_4188_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(lean_object* v_00_u03b1_4190_, lean_object* v_name_4191_, uint8_t v_bi_4192_, lean_object* v_type_4193_, lean_object* v_k_4194_, uint8_t v_kind_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___redArg(v_name_4191_, v_bi_4192_, v_type_4193_, v_k_4194_, v_kind_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4202_, lean_object* v_name_4203_, lean_object* v_bi_4204_, lean_object* v_type_4205_, lean_object* v_k_4206_, lean_object* v_kind_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_){
_start:
{
uint8_t v_bi_boxed_4213_; uint8_t v_kind_boxed_4214_; lean_object* v_res_4215_; 
v_bi_boxed_4213_ = lean_unbox(v_bi_4204_);
v_kind_boxed_4214_ = lean_unbox(v_kind_4207_);
v_res_4215_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4(v_00_u03b1_4202_, v_name_4203_, v_bi_boxed_4213_, v_type_4205_, v_k_4206_, v_kind_boxed_4214_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
lean_dec(v___y_4211_);
lean_dec_ref(v___y_4210_);
lean_dec(v___y_4209_);
lean_dec_ref(v___y_4208_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(lean_object* v_00_u03b1_4216_, lean_object* v_name_4217_, lean_object* v_type_4218_, lean_object* v_k_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v___x_4225_; 
v___x_4225_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___redArg(v_name_4217_, v_type_4218_, v_k_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
return v___x_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2___boxed(lean_object* v_00_u03b1_4226_, lean_object* v_name_4227_, lean_object* v_type_4228_, lean_object* v_k_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_){
_start:
{
lean_object* v_res_4235_; 
v_res_4235_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2(v_00_u03b1_4226_, v_name_4227_, v_type_4228_, v_k_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v___y_4230_);
return v_res_4235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(lean_object* v_00_u03b1_4236_, lean_object* v_inst_4237_, lean_object* v_declInfos_4238_, lean_object* v_k_4239_, uint8_t v_kind_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v___x_4246_; 
v___x_4246_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___redArg(v_inst_4237_, v_declInfos_4238_, v_k_4239_, v_kind_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4247_, lean_object* v_inst_4248_, lean_object* v_declInfos_4249_, lean_object* v_k_4250_, lean_object* v_kind_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_){
_start:
{
uint8_t v_kind_boxed_4257_; lean_object* v_res_4258_; 
v_kind_boxed_4257_ = lean_unbox(v_kind_4251_);
v_res_4258_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2(v_00_u03b1_4247_, v_inst_4248_, v_declInfos_4249_, v_k_4250_, v_kind_boxed_4257_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v___y_4252_);
return v_res_4258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(lean_object* v_00_u03b1_4259_, lean_object* v_acc_4260_, lean_object* v_declInfos_4261_, lean_object* v_k_4262_, uint8_t v_kind_4263_, lean_object* v_inst_4264_, lean_object* v_name_4265_, uint8_t v_bi_4266_, lean_object* v_type_4267_, uint8_t v_kind_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; 
v___x_4274_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___redArg(v_acc_4260_, v_declInfos_4261_, v_k_4262_, v_kind_4263_, v_inst_4264_, v_name_4265_, v_bi_4266_, v_type_4267_, v_kind_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
return v___x_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8___boxed(lean_object* v_00_u03b1_4275_, lean_object* v_acc_4276_, lean_object* v_declInfos_4277_, lean_object* v_k_4278_, lean_object* v_kind_4279_, lean_object* v_inst_4280_, lean_object* v_name_4281_, lean_object* v_bi_4282_, lean_object* v_type_4283_, lean_object* v_kind_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
uint8_t v_kind_boxed_4290_; uint8_t v_bi_boxed_4291_; uint8_t v_kind_boxed_4292_; lean_object* v_res_4293_; 
v_kind_boxed_4290_ = lean_unbox(v_kind_4279_);
v_bi_boxed_4291_ = lean_unbox(v_bi_4282_);
v_kind_boxed_4292_ = lean_unbox(v_kind_4284_);
v_res_4293_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__2_spec__4___at___00__private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4_spec__8(v_00_u03b1_4275_, v_acc_4276_, v_declInfos_4277_, v_k_4278_, v_kind_boxed_4290_, v_inst_4280_, v_name_4281_, v_bi_boxed_4291_, v_type_4283_, v_kind_boxed_4292_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_4294_, lean_object* v_declInfos_4295_, lean_object* v_k_4296_, uint8_t v_kind_4297_, lean_object* v_inst_4298_, lean_object* v_acc_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___redArg(v_declInfos_4295_, v_k_4296_, v_kind_4297_, v_inst_4298_, v_acc_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_4306_, lean_object* v_declInfos_4307_, lean_object* v_k_4308_, lean_object* v_kind_4309_, lean_object* v_inst_4310_, lean_object* v_acc_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
uint8_t v_kind_boxed_4317_; lean_object* v_res_4318_; 
v_kind_boxed_4317_ = lean_unbox(v_kind_4309_);
v_res_4318_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Elab_ComputedFields_mkComputedFieldOverrides_spec__1_spec__2_spec__4(v_00_u03b1_4306_, v_declInfos_4307_, v_k_4308_, v_kind_boxed_4317_, v_inst_4310_, v_acc_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
return v_res_4318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(lean_object* v_as_4319_, size_t v_sz_4320_, size_t v_i_4321_, lean_object* v_b_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v_a_4326_; uint8_t v___x_4330_; 
v___x_4330_ = lean_usize_dec_lt(v_i_4321_, v_sz_4320_);
if (v___x_4330_ == 0)
{
lean_object* v___x_4331_; 
v___x_4331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4331_, 0, v_b_4322_);
return v___x_4331_;
}
else
{
lean_object* v___x_4332_; lean_object* v_env_4333_; lean_object* v_a_4334_; uint8_t v___x_4335_; 
v___x_4332_ = lean_st_ref_get(v___y_4323_);
v_env_4333_ = lean_ctor_get(v___x_4332_, 0);
lean_inc_ref(v_env_4333_);
lean_dec(v___x_4332_);
v_a_4334_ = lean_array_uget_borrowed(v_as_4319_, v_i_4321_);
lean_inc(v_a_4334_);
v___x_4335_ = l_Lean_isExtern(v_env_4333_, v_a_4334_);
if (v___x_4335_ == 0)
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; 
v___x_4336_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
lean_inc(v_a_4334_);
v___x_4337_ = l_Lean_Name_append(v_a_4334_, v___x_4336_);
v___x_4338_ = lean_array_push(v_b_4322_, v___x_4337_);
v_a_4326_ = v___x_4338_;
goto v___jp_4325_;
}
else
{
v_a_4326_ = v_b_4322_;
goto v___jp_4325_;
}
}
v___jp_4325_:
{
size_t v___x_4327_; size_t v___x_4328_; 
v___x_4327_ = ((size_t)1ULL);
v___x_4328_ = lean_usize_add(v_i_4321_, v___x_4327_);
v_i_4321_ = v___x_4328_;
v_b_4322_ = v_a_4326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg___boxed(lean_object* v_as_4339_, lean_object* v_sz_4340_, lean_object* v_i_4341_, lean_object* v_b_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
size_t v_sz_boxed_4345_; size_t v_i_boxed_4346_; lean_object* v_res_4347_; 
v_sz_boxed_4345_ = lean_unbox_usize(v_sz_4340_);
lean_dec(v_sz_4340_);
v_i_boxed_4346_ = lean_unbox_usize(v_i_4341_);
lean_dec(v_i_4341_);
v_res_4347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4339_, v_sz_boxed_4345_, v_i_boxed_4346_, v_b_4342_, v___y_4343_);
lean_dec(v___y_4343_);
lean_dec_ref(v_as_4339_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(lean_object* v_as_x27_4348_, lean_object* v_b_4349_){
_start:
{
if (lean_obj_tag(v_as_x27_4348_) == 0)
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4351_, 0, v_b_4349_);
return v___x_4351_;
}
else
{
lean_object* v_head_4352_; lean_object* v_tail_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v_head_4352_ = lean_ctor_get(v_as_x27_4348_, 0);
lean_inc(v_head_4352_);
v_tail_4353_ = lean_ctor_get(v_as_x27_4348_, 1);
lean_inc(v_tail_4353_);
lean_dec_ref(v_as_x27_4348_);
v___x_4354_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4355_ = l_Lean_Name_append(v_head_4352_, v___x_4354_);
v___x_4356_ = lean_array_push(v_b_4349_, v___x_4355_);
v_as_x27_4348_ = v_tail_4353_;
v_b_4349_ = v___x_4356_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg___boxed(lean_object* v_as_x27_4358_, lean_object* v_b_4359_, lean_object* v___y_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4358_, v_b_4359_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(lean_object* v_as_4362_, size_t v_sz_4363_, size_t v_i_4364_, lean_object* v_b_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_){
_start:
{
uint8_t v___x_4371_; 
v___x_4371_ = lean_usize_dec_lt(v_i_4364_, v_sz_4363_);
if (v___x_4371_ == 0)
{
lean_object* v___x_4372_; 
v___x_4372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4372_, 0, v_b_4365_);
return v___x_4372_;
}
else
{
lean_object* v_a_4373_; lean_object* v_fst_4374_; lean_object* v_snd_4375_; lean_object* v___x_4376_; 
v_a_4373_ = lean_array_uget_borrowed(v_as_4362_, v_i_4364_);
v_fst_4374_ = lean_ctor_get(v_a_4373_, 0);
v_snd_4375_ = lean_ctor_get(v_a_4373_, 1);
lean_inc(v_fst_4374_);
v___x_4376_ = l_Lean_getConstInfoInduct___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__3(v_fst_4374_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
if (lean_obj_tag(v___x_4376_) == 0)
{
lean_object* v_a_4377_; lean_object* v_ctors_4378_; lean_object* v___x_4379_; 
v_a_4377_ = lean_ctor_get(v___x_4376_, 0);
lean_inc(v_a_4377_);
lean_dec_ref(v___x_4376_);
v_ctors_4378_ = lean_ctor_get(v_a_4377_, 4);
lean_inc(v_ctors_4378_);
lean_dec(v_a_4377_);
v___x_4379_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_ctors_4378_, v_b_4365_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_object* v_a_4380_; size_t v_sz_4381_; size_t v___x_4382_; lean_object* v___x_4383_; 
v_a_4380_ = lean_ctor_get(v___x_4379_, 0);
lean_inc(v_a_4380_);
lean_dec_ref(v___x_4379_);
v_sz_4381_ = lean_array_size(v_snd_4375_);
v___x_4382_ = ((size_t)0ULL);
v___x_4383_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_snd_4375_, v_sz_4381_, v___x_4382_, v_a_4380_, v___y_4369_);
if (lean_obj_tag(v___x_4383_) == 0)
{
lean_object* v_a_4384_; size_t v___x_4385_; size_t v___x_4386_; 
v_a_4384_ = lean_ctor_get(v___x_4383_, 0);
lean_inc(v_a_4384_);
lean_dec_ref(v___x_4383_);
v___x_4385_ = ((size_t)1ULL);
v___x_4386_ = lean_usize_add(v_i_4364_, v___x_4385_);
v_i_4364_ = v___x_4386_;
v_b_4365_ = v_a_4384_;
goto _start;
}
else
{
return v___x_4383_;
}
}
else
{
return v___x_4379_;
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec_ref(v_b_4365_);
v_a_4388_ = lean_ctor_get(v___x_4376_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4376_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4376_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4376_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6___boxed(lean_object* v_as_4396_, lean_object* v_sz_4397_, lean_object* v_i_4398_, lean_object* v_b_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
size_t v_sz_boxed_4405_; size_t v_i_boxed_4406_; lean_object* v_res_4407_; 
v_sz_boxed_4405_ = lean_unbox_usize(v_sz_4397_);
lean_dec(v_sz_4397_);
v_i_boxed_4406_ = lean_unbox_usize(v_i_4398_);
lean_dec(v_i_4398_);
v_res_4407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_as_4396_, v_sz_boxed_4405_, v_i_boxed_4406_, v_b_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_);
lean_dec(v___y_4403_);
lean_dec_ref(v___y_4402_);
lean_dec(v___y_4401_);
lean_dec_ref(v___y_4400_);
lean_dec_ref(v_as_4396_);
return v_res_4407_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(uint8_t v___y_4415_, uint8_t v_suppressElabErrors_4416_, lean_object* v_x_4417_){
_start:
{
if (lean_obj_tag(v_x_4417_) == 1)
{
lean_object* v_pre_4418_; 
v_pre_4418_ = lean_ctor_get(v_x_4417_, 0);
switch(lean_obj_tag(v_pre_4418_))
{
case 1:
{
lean_object* v_pre_4419_; 
v_pre_4419_ = lean_ctor_get(v_pre_4418_, 0);
switch(lean_obj_tag(v_pre_4419_))
{
case 0:
{
lean_object* v_str_4420_; lean_object* v_str_4421_; lean_object* v___x_4422_; uint8_t v___x_4423_; 
v_str_4420_ = lean_ctor_get(v_x_4417_, 1);
v_str_4421_ = lean_ctor_get(v_pre_4418_, 1);
v___x_4422_ = ((lean_object*)(l_Lean_Elab_ComputedFields_initFn___closed__5_00___x40_Lean_Elab_ComputedFields_4242877025____hygCtx___hyg_2_));
v___x_4423_ = lean_string_dec_eq(v_str_4421_, v___x_4422_);
if (v___x_4423_ == 0)
{
lean_object* v___x_4424_; uint8_t v___x_4425_; 
v___x_4424_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__0));
v___x_4425_ = lean_string_dec_eq(v_str_4421_, v___x_4424_);
if (v___x_4425_ == 0)
{
return v___y_4415_;
}
else
{
lean_object* v___x_4426_; uint8_t v___x_4427_; 
v___x_4426_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__1));
v___x_4427_ = lean_string_dec_eq(v_str_4420_, v___x_4426_);
if (v___x_4427_ == 0)
{
return v___y_4415_;
}
else
{
return v_suppressElabErrors_4416_;
}
}
}
else
{
lean_object* v___x_4428_; uint8_t v___x_4429_; 
v___x_4428_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__2));
v___x_4429_ = lean_string_dec_eq(v_str_4420_, v___x_4428_);
if (v___x_4429_ == 0)
{
return v___y_4415_;
}
else
{
return v_suppressElabErrors_4416_;
}
}
}
case 1:
{
lean_object* v_pre_4430_; 
v_pre_4430_ = lean_ctor_get(v_pre_4419_, 0);
if (lean_obj_tag(v_pre_4430_) == 0)
{
lean_object* v_str_4431_; lean_object* v_str_4432_; lean_object* v_str_4433_; lean_object* v___x_4434_; uint8_t v___x_4435_; 
v_str_4431_ = lean_ctor_get(v_x_4417_, 1);
v_str_4432_ = lean_ctor_get(v_pre_4418_, 1);
v_str_4433_ = lean_ctor_get(v_pre_4419_, 1);
v___x_4434_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__3));
v___x_4435_ = lean_string_dec_eq(v_str_4433_, v___x_4434_);
if (v___x_4435_ == 0)
{
return v___y_4415_;
}
else
{
lean_object* v___x_4436_; uint8_t v___x_4437_; 
v___x_4436_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__4));
v___x_4437_ = lean_string_dec_eq(v_str_4432_, v___x_4436_);
if (v___x_4437_ == 0)
{
return v___y_4415_;
}
else
{
lean_object* v___x_4438_; uint8_t v___x_4439_; 
v___x_4438_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__5));
v___x_4439_ = lean_string_dec_eq(v_str_4431_, v___x_4438_);
if (v___x_4439_ == 0)
{
return v___y_4415_;
}
else
{
return v_suppressElabErrors_4416_;
}
}
}
}
else
{
return v___y_4415_;
}
}
default: 
{
return v___y_4415_;
}
}
}
case 0:
{
lean_object* v_str_4440_; lean_object* v___x_4441_; uint8_t v___x_4442_; 
v_str_4440_ = lean_ctor_get(v_x_4417_, 1);
v___x_4441_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___closed__6));
v___x_4442_ = lean_string_dec_eq(v_str_4440_, v___x_4441_);
if (v___x_4442_ == 0)
{
return v___y_4415_;
}
else
{
return v_suppressElabErrors_4416_;
}
}
default: 
{
return v___y_4415_;
}
}
}
else
{
return v___y_4415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed(lean_object* v___y_4443_, lean_object* v_suppressElabErrors_4444_, lean_object* v_x_4445_){
_start:
{
uint8_t v___y_7410__boxed_4446_; uint8_t v_suppressElabErrors_boxed_4447_; uint8_t v_res_4448_; lean_object* v_r_4449_; 
v___y_7410__boxed_4446_ = lean_unbox(v___y_4443_);
v_suppressElabErrors_boxed_4447_ = lean_unbox(v_suppressElabErrors_4444_);
v_res_4448_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0(v___y_7410__boxed_4446_, v_suppressElabErrors_boxed_4447_, v_x_4445_);
lean_dec(v_x_4445_);
v_r_4449_ = lean_box(v_res_4448_);
return v_r_4449_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(lean_object* v_opts_4450_, lean_object* v_opt_4451_){
_start:
{
lean_object* v_name_4452_; lean_object* v_defValue_4453_; lean_object* v_map_4454_; lean_object* v___x_4455_; 
v_name_4452_ = lean_ctor_get(v_opt_4451_, 0);
v_defValue_4453_ = lean_ctor_get(v_opt_4451_, 1);
v_map_4454_ = lean_ctor_get(v_opts_4450_, 0);
v___x_4455_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_4454_, v_name_4452_);
if (lean_obj_tag(v___x_4455_) == 0)
{
uint8_t v___x_4456_; 
v___x_4456_ = lean_unbox(v_defValue_4453_);
return v___x_4456_;
}
else
{
lean_object* v_val_4457_; 
v_val_4457_ = lean_ctor_get(v___x_4455_, 0);
lean_inc(v_val_4457_);
lean_dec_ref(v___x_4455_);
if (lean_obj_tag(v_val_4457_) == 1)
{
uint8_t v_v_4458_; 
v_v_4458_ = lean_ctor_get_uint8(v_val_4457_, 0);
lean_dec_ref(v_val_4457_);
return v_v_4458_;
}
else
{
uint8_t v___x_4459_; 
lean_dec(v_val_4457_);
v___x_4459_ = lean_unbox(v_defValue_4453_);
return v___x_4459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8___boxed(lean_object* v_opts_4460_, lean_object* v_opt_4461_){
_start:
{
uint8_t v_res_4462_; lean_object* v_r_4463_; 
v_res_4462_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_opts_4460_, v_opt_4461_);
lean_dec_ref(v_opt_4461_);
lean_dec_ref(v_opts_4460_);
v_r_4463_ = lean_box(v_res_4462_);
return v_r_4463_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(lean_object* v_ref_4465_, lean_object* v_msgData_4466_, uint8_t v_severity_4467_, uint8_t v_isSilent_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_){
_start:
{
lean_object* v___y_4475_; uint8_t v___y_4476_; lean_object* v___y_4477_; lean_object* v___y_4478_; lean_object* v___y_4479_; lean_object* v___y_4480_; uint8_t v___y_4481_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4511_; uint8_t v___y_4512_; uint8_t v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; uint8_t v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4536_; uint8_t v___y_4537_; lean_object* v___y_4538_; uint8_t v___y_4539_; lean_object* v___y_4540_; uint8_t v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4547_; uint8_t v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; uint8_t v___y_4551_; lean_object* v___y_4552_; uint8_t v___y_4553_; uint8_t v___x_4558_; uint8_t v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; uint8_t v___y_4565_; uint8_t v___y_4566_; uint8_t v___y_4568_; uint8_t v___x_4583_; 
v___x_4558_ = 2;
v___x_4583_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4467_, v___x_4558_);
if (v___x_4583_ == 0)
{
v___y_4568_ = v___x_4583_;
goto v___jp_4567_;
}
else
{
uint8_t v___x_4584_; 
lean_inc_ref(v_msgData_4466_);
v___x_4584_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4466_);
v___y_4568_ = v___x_4584_;
goto v___jp_4567_;
}
v___jp_4474_:
{
lean_object* v___x_4484_; lean_object* v_currNamespace_4485_; lean_object* v_openDecls_4486_; lean_object* v_env_4487_; lean_object* v_nextMacroScope_4488_; lean_object* v_ngen_4489_; lean_object* v_auxDeclNGen_4490_; lean_object* v_traceState_4491_; lean_object* v_cache_4492_; lean_object* v_messages_4493_; lean_object* v_infoState_4494_; lean_object* v_snapshotTasks_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4509_; 
v___x_4484_ = lean_st_ref_take(v___y_4483_);
v_currNamespace_4485_ = lean_ctor_get(v___y_4482_, 6);
v_openDecls_4486_ = lean_ctor_get(v___y_4482_, 7);
v_env_4487_ = lean_ctor_get(v___x_4484_, 0);
v_nextMacroScope_4488_ = lean_ctor_get(v___x_4484_, 1);
v_ngen_4489_ = lean_ctor_get(v___x_4484_, 2);
v_auxDeclNGen_4490_ = lean_ctor_get(v___x_4484_, 3);
v_traceState_4491_ = lean_ctor_get(v___x_4484_, 4);
v_cache_4492_ = lean_ctor_get(v___x_4484_, 5);
v_messages_4493_ = lean_ctor_get(v___x_4484_, 6);
v_infoState_4494_ = lean_ctor_get(v___x_4484_, 7);
v_snapshotTasks_4495_ = lean_ctor_get(v___x_4484_, 8);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4497_ = v___x_4484_;
v_isShared_4498_ = v_isSharedCheck_4509_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_snapshotTasks_4495_);
lean_inc(v_infoState_4494_);
lean_inc(v_messages_4493_);
lean_inc(v_cache_4492_);
lean_inc(v_traceState_4491_);
lean_inc(v_auxDeclNGen_4490_);
lean_inc(v_ngen_4489_);
lean_inc(v_nextMacroScope_4488_);
lean_inc(v_env_4487_);
lean_dec(v___x_4484_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4509_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4504_; 
lean_inc(v_openDecls_4486_);
lean_inc(v_currNamespace_4485_);
v___x_4499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4499_, 0, v_currNamespace_4485_);
lean_ctor_set(v___x_4499_, 1, v_openDecls_4486_);
v___x_4500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
lean_ctor_set(v___x_4500_, 1, v___y_4475_);
lean_inc_ref(v___y_4478_);
v___x_4501_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_4501_, 0, v___y_4478_);
lean_ctor_set(v___x_4501_, 1, v___y_4480_);
lean_ctor_set(v___x_4501_, 2, v___y_4477_);
lean_ctor_set(v___x_4501_, 3, v___y_4479_);
lean_ctor_set(v___x_4501_, 4, v___x_4500_);
lean_ctor_set_uint8(v___x_4501_, sizeof(void*)*5, v___y_4481_);
lean_ctor_set_uint8(v___x_4501_, sizeof(void*)*5 + 1, v___y_4476_);
lean_ctor_set_uint8(v___x_4501_, sizeof(void*)*5 + 2, v_isSilent_4468_);
v___x_4502_ = l_Lean_MessageLog_add(v___x_4501_, v_messages_4493_);
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 6, v___x_4502_);
v___x_4504_ = v___x_4497_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_env_4487_);
lean_ctor_set(v_reuseFailAlloc_4508_, 1, v_nextMacroScope_4488_);
lean_ctor_set(v_reuseFailAlloc_4508_, 2, v_ngen_4489_);
lean_ctor_set(v_reuseFailAlloc_4508_, 3, v_auxDeclNGen_4490_);
lean_ctor_set(v_reuseFailAlloc_4508_, 4, v_traceState_4491_);
lean_ctor_set(v_reuseFailAlloc_4508_, 5, v_cache_4492_);
lean_ctor_set(v_reuseFailAlloc_4508_, 6, v___x_4502_);
lean_ctor_set(v_reuseFailAlloc_4508_, 7, v_infoState_4494_);
lean_ctor_set(v_reuseFailAlloc_4508_, 8, v_snapshotTasks_4495_);
v___x_4504_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; 
v___x_4505_ = lean_st_ref_set(v___y_4483_, v___x_4504_);
v___x_4506_ = lean_box(0);
v___x_4507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
return v___x_4507_;
}
}
}
v___jp_4510_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4534_; 
v___x_4519_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_4466_);
v___x_4520_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ComputedFields_getComputedFieldValue_spec__1_spec__2(v___x_4519_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_);
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4523_ = v___x_4520_;
v_isShared_4524_ = v_isSharedCheck_4534_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4520_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4534_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
lean_inc_ref(v___y_4517_);
v___x_4525_ = l_Lean_FileMap_toPosition(v___y_4517_, v___y_4514_);
lean_dec(v___y_4514_);
lean_inc_ref(v___y_4517_);
v___x_4526_ = l_Lean_FileMap_toPosition(v___y_4517_, v___y_4518_);
lean_dec(v___y_4518_);
v___x_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
v___x_4528_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___closed__0));
if (v___y_4512_ == 0)
{
lean_del_object(v___x_4523_);
lean_dec_ref(v___y_4511_);
v___y_4475_ = v_a_4521_;
v___y_4476_ = v___y_4513_;
v___y_4477_ = v___x_4527_;
v___y_4478_ = v___y_4515_;
v___y_4479_ = v___x_4528_;
v___y_4480_ = v___x_4525_;
v___y_4481_ = v___y_4516_;
v___y_4482_ = v___y_4471_;
v___y_4483_ = v___y_4472_;
goto v___jp_4474_;
}
else
{
uint8_t v___x_4529_; 
lean_inc(v_a_4521_);
v___x_4529_ = l_Lean_MessageData_hasTag(v___y_4511_, v_a_4521_);
if (v___x_4529_ == 0)
{
lean_object* v___x_4530_; lean_object* v___x_4532_; 
lean_dec_ref(v___x_4527_);
lean_dec_ref(v___x_4525_);
lean_dec(v_a_4521_);
v___x_4530_ = lean_box(0);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4530_);
v___x_4532_ = v___x_4523_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4530_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
else
{
lean_del_object(v___x_4523_);
v___y_4475_ = v_a_4521_;
v___y_4476_ = v___y_4513_;
v___y_4477_ = v___x_4527_;
v___y_4478_ = v___y_4515_;
v___y_4479_ = v___x_4528_;
v___y_4480_ = v___x_4525_;
v___y_4481_ = v___y_4516_;
v___y_4482_ = v___y_4471_;
v___y_4483_ = v___y_4472_;
goto v___jp_4474_;
}
}
}
}
v___jp_4535_:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_Syntax_getTailPos_x3f(v___y_4538_, v___y_4541_);
lean_dec(v___y_4538_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_inc(v___y_4543_);
v___y_4511_ = v___y_4536_;
v___y_4512_ = v___y_4537_;
v___y_4513_ = v___y_4539_;
v___y_4514_ = v___y_4543_;
v___y_4515_ = v___y_4540_;
v___y_4516_ = v___y_4541_;
v___y_4517_ = v___y_4542_;
v___y_4518_ = v___y_4543_;
goto v___jp_4510_;
}
else
{
lean_object* v_val_4545_; 
v_val_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc(v_val_4545_);
lean_dec_ref(v___x_4544_);
v___y_4511_ = v___y_4536_;
v___y_4512_ = v___y_4537_;
v___y_4513_ = v___y_4539_;
v___y_4514_ = v___y_4543_;
v___y_4515_ = v___y_4540_;
v___y_4516_ = v___y_4541_;
v___y_4517_ = v___y_4542_;
v___y_4518_ = v_val_4545_;
goto v___jp_4510_;
}
}
v___jp_4546_:
{
lean_object* v_ref_4554_; lean_object* v___x_4555_; 
v_ref_4554_ = l_Lean_replaceRef(v_ref_4465_, v___y_4549_);
v___x_4555_ = l_Lean_Syntax_getPos_x3f(v_ref_4554_, v___y_4551_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v___x_4556_; 
v___x_4556_ = lean_unsigned_to_nat(0u);
v___y_4536_ = v___y_4547_;
v___y_4537_ = v___y_4548_;
v___y_4538_ = v_ref_4554_;
v___y_4539_ = v___y_4553_;
v___y_4540_ = v___y_4550_;
v___y_4541_ = v___y_4551_;
v___y_4542_ = v___y_4552_;
v___y_4543_ = v___x_4556_;
goto v___jp_4535_;
}
else
{
lean_object* v_val_4557_; 
v_val_4557_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_val_4557_);
lean_dec_ref(v___x_4555_);
v___y_4536_ = v___y_4547_;
v___y_4537_ = v___y_4548_;
v___y_4538_ = v_ref_4554_;
v___y_4539_ = v___y_4553_;
v___y_4540_ = v___y_4550_;
v___y_4541_ = v___y_4551_;
v___y_4542_ = v___y_4552_;
v___y_4543_ = v_val_4557_;
goto v___jp_4535_;
}
}
v___jp_4559_:
{
if (v___y_4566_ == 0)
{
v___y_4547_ = v___y_4561_;
v___y_4548_ = v___y_4560_;
v___y_4549_ = v___y_4562_;
v___y_4550_ = v___y_4563_;
v___y_4551_ = v___y_4565_;
v___y_4552_ = v___y_4564_;
v___y_4553_ = v_severity_4467_;
goto v___jp_4546_;
}
else
{
v___y_4547_ = v___y_4561_;
v___y_4548_ = v___y_4560_;
v___y_4549_ = v___y_4562_;
v___y_4550_ = v___y_4563_;
v___y_4551_ = v___y_4565_;
v___y_4552_ = v___y_4564_;
v___y_4553_ = v___x_4558_;
goto v___jp_4546_;
}
}
v___jp_4567_:
{
if (v___y_4568_ == 0)
{
lean_object* v_fileName_4569_; lean_object* v_fileMap_4570_; lean_object* v_options_4571_; lean_object* v_ref_4572_; uint8_t v_suppressElabErrors_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___f_4576_; uint8_t v___x_4577_; uint8_t v___x_4578_; 
v_fileName_4569_ = lean_ctor_get(v___y_4471_, 0);
v_fileMap_4570_ = lean_ctor_get(v___y_4471_, 1);
v_options_4571_ = lean_ctor_get(v___y_4471_, 2);
v_ref_4572_ = lean_ctor_get(v___y_4471_, 5);
v_suppressElabErrors_4573_ = lean_ctor_get_uint8(v___y_4471_, sizeof(void*)*14 + 1);
v___x_4574_ = lean_box(v___y_4568_);
v___x_4575_ = lean_box(v_suppressElabErrors_4573_);
v___f_4576_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_4576_, 0, v___x_4574_);
lean_closure_set(v___f_4576_, 1, v___x_4575_);
v___x_4577_ = 1;
v___x_4578_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4467_, v___x_4577_);
if (v___x_4578_ == 0)
{
v___y_4560_ = v_suppressElabErrors_4573_;
v___y_4561_ = v___f_4576_;
v___y_4562_ = v_ref_4572_;
v___y_4563_ = v_fileName_4569_;
v___y_4564_ = v_fileMap_4570_;
v___y_4565_ = v___y_4568_;
v___y_4566_ = v___x_4578_;
goto v___jp_4559_;
}
else
{
lean_object* v___x_4579_; uint8_t v___x_4580_; 
v___x_4579_ = l_Lean_warningAsError;
v___x_4580_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3_spec__8(v_options_4571_, v___x_4579_);
v___y_4560_ = v_suppressElabErrors_4573_;
v___y_4561_ = v___f_4576_;
v___y_4562_ = v_ref_4572_;
v___y_4563_ = v_fileName_4569_;
v___y_4564_ = v_fileMap_4570_;
v___y_4565_ = v___y_4568_;
v___y_4566_ = v___x_4580_;
goto v___jp_4559_;
}
}
else
{
lean_object* v___x_4581_; lean_object* v___x_4582_; 
lean_dec_ref(v_msgData_4466_);
v___x_4581_ = lean_box(0);
v___x_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
return v___x_4582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3___boxed(lean_object* v_ref_4585_, lean_object* v_msgData_4586_, lean_object* v_severity_4587_, lean_object* v_isSilent_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_){
_start:
{
uint8_t v_severity_boxed_4594_; uint8_t v_isSilent_boxed_4595_; lean_object* v_res_4596_; 
v_severity_boxed_4594_ = lean_unbox(v_severity_4587_);
v_isSilent_boxed_4595_ = lean_unbox(v_isSilent_4588_);
v_res_4596_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4585_, v_msgData_4586_, v_severity_boxed_4594_, v_isSilent_boxed_4595_, v___y_4589_, v___y_4590_, v___y_4591_, v___y_4592_);
lean_dec(v___y_4592_);
lean_dec_ref(v___y_4591_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v_ref_4585_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(lean_object* v_msgData_4597_, uint8_t v_severity_4598_, uint8_t v_isSilent_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_){
_start:
{
lean_object* v_ref_4605_; lean_object* v___x_4606_; 
v_ref_4605_ = lean_ctor_get(v___y_4602_, 5);
v___x_4606_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2_spec__3(v_ref_4605_, v_msgData_4597_, v_severity_4598_, v_isSilent_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
return v___x_4606_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2___boxed(lean_object* v_msgData_4607_, lean_object* v_severity_4608_, lean_object* v_isSilent_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
uint8_t v_severity_boxed_4615_; uint8_t v_isSilent_boxed_4616_; lean_object* v_res_4617_; 
v_severity_boxed_4615_ = lean_unbox(v_severity_4608_);
v_isSilent_boxed_4616_ = lean_unbox(v_isSilent_4609_);
v_res_4617_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4607_, v_severity_boxed_4615_, v_isSilent_boxed_4616_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(lean_object* v_msgData_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_){
_start:
{
uint8_t v___x_4624_; uint8_t v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = 2;
v___x_4625_ = 0;
v___x_4626_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2_spec__2(v_msgData_4618_, v___x_4624_, v___x_4625_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2___boxed(lean_object* v_msgData_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_){
_start:
{
lean_object* v_res_4633_; 
v_res_4633_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v_msgData_4627_, v___y_4628_, v___y_4629_, v___y_4630_, v___y_4631_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v___y_4629_);
lean_dec_ref(v___y_4628_);
return v_res_4633_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1(void){
_start:
{
lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4635_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__0));
v___x_4636_ = l_Lean_stringToMessageData(v___x_4635_);
return v___x_4636_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3(void){
_start:
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__2));
v___x_4639_ = l_Lean_stringToMessageData(v___x_4638_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(lean_object* v_as_4640_, size_t v_sz_4641_, size_t v_i_4642_, lean_object* v_b_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v_a_4650_; uint8_t v___x_4654_; 
v___x_4654_ = lean_usize_dec_lt(v_i_4642_, v_sz_4641_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; 
v___x_4655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4655_, 0, v_b_4643_);
return v___x_4655_;
}
else
{
lean_object* v___x_4656_; lean_object* v_env_4657_; lean_object* v___x_4658_; lean_object* v_a_4659_; lean_object* v___x_4660_; uint8_t v___x_4661_; 
v___x_4656_ = lean_st_ref_get(v___y_4647_);
v_env_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc_ref(v_env_4657_);
lean_dec(v___x_4656_);
v___x_4658_ = lean_box(0);
v_a_4659_ = lean_array_uget_borrowed(v_as_4640_, v_i_4642_);
v___x_4660_ = l_Lean_Elab_ComputedFields_computedFieldAttr;
lean_inc(v_a_4659_);
v___x_4661_ = l_Lean_TagAttribute_hasTag(v___x_4660_, v_env_4657_, v_a_4659_);
if (v___x_4661_ == 0)
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4662_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__1);
lean_inc(v_a_4659_);
v___x_4663_ = l_Lean_MessageData_ofName(v_a_4659_);
v___x_4664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4662_);
lean_ctor_set(v___x_4664_, 1, v___x_4663_);
v___x_4665_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___closed__3);
v___x_4666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4664_);
lean_ctor_set(v___x_4666_, 1, v___x_4665_);
v___x_4667_ = l_Lean_logError___at___00Lean_Elab_ComputedFields_setComputedFields_spec__2(v___x_4666_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_dec_ref(v___x_4667_);
v_a_4650_ = v___x_4658_;
goto v___jp_4649_;
}
else
{
return v___x_4667_;
}
}
else
{
v_a_4650_ = v___x_4658_;
goto v___jp_4649_;
}
}
v___jp_4649_:
{
size_t v___x_4651_; size_t v___x_4652_; 
v___x_4651_ = ((size_t)1ULL);
v___x_4652_ = lean_usize_add(v_i_4642_, v___x_4651_);
v_i_4642_ = v___x_4652_;
v_b_4643_ = v_a_4650_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3___boxed(lean_object* v_as_4668_, lean_object* v_sz_4669_, lean_object* v_i_4670_, lean_object* v_b_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
size_t v_sz_boxed_4677_; size_t v_i_boxed_4678_; lean_object* v_res_4679_; 
v_sz_boxed_4677_ = lean_unbox_usize(v_sz_4669_);
lean_dec(v_sz_4669_);
v_i_boxed_4678_ = lean_unbox_usize(v_i_4670_);
lean_dec(v_i_4670_);
v_res_4679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_as_4668_, v_sz_boxed_4677_, v_i_boxed_4678_, v_b_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
lean_dec_ref(v___y_4672_);
lean_dec_ref(v_as_4668_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(lean_object* v_as_4680_, size_t v_sz_4681_, size_t v_i_4682_, lean_object* v_b_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
uint8_t v___x_4689_; 
v___x_4689_ = lean_usize_dec_lt(v_i_4682_, v_sz_4681_);
if (v___x_4689_ == 0)
{
lean_object* v___x_4690_; 
v___x_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4690_, 0, v_b_4683_);
return v___x_4690_;
}
else
{
lean_object* v_a_4691_; lean_object* v_fst_4692_; lean_object* v_snd_4693_; lean_object* v___x_4694_; size_t v_sz_4695_; size_t v___x_4696_; lean_object* v___x_4697_; 
v_a_4691_ = lean_array_uget_borrowed(v_as_4680_, v_i_4682_);
v_fst_4692_ = lean_ctor_get(v_a_4691_, 0);
v_snd_4693_ = lean_ctor_get(v_a_4691_, 1);
v___x_4694_ = lean_box(0);
v_sz_4695_ = lean_array_size(v_snd_4693_);
v___x_4696_ = ((size_t)0ULL);
v___x_4697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__3(v_snd_4693_, v_sz_4695_, v___x_4696_, v___x_4694_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v___x_4698_; 
lean_dec_ref(v___x_4697_);
lean_inc(v_snd_4693_);
lean_inc(v_fst_4692_);
v___x_4698_ = l_Lean_Elab_ComputedFields_mkComputedFieldOverrides(v_fst_4692_, v_snd_4693_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
if (lean_obj_tag(v___x_4698_) == 0)
{
size_t v___x_4699_; size_t v___x_4700_; 
lean_dec_ref(v___x_4698_);
v___x_4699_ = ((size_t)1ULL);
v___x_4700_ = lean_usize_add(v_i_4682_, v___x_4699_);
v_i_4682_ = v___x_4700_;
v_b_4683_ = v___x_4694_;
goto _start;
}
else
{
return v___x_4698_;
}
}
else
{
return v___x_4697_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4___boxed(lean_object* v_as_4702_, lean_object* v_sz_4703_, lean_object* v_i_4704_, lean_object* v_b_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
size_t v_sz_boxed_4711_; size_t v_i_boxed_4712_; lean_object* v_res_4713_; 
v_sz_boxed_4711_ = lean_unbox_usize(v_sz_4703_);
lean_dec(v_sz_4703_);
v_i_boxed_4712_ = lean_unbox_usize(v_i_4704_);
lean_dec(v_i_4704_);
v_res_4713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_as_4702_, v_sz_boxed_4711_, v_i_boxed_4712_, v_b_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec(v___y_4707_);
lean_dec_ref(v___y_4706_);
lean_dec_ref(v_as_4702_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(size_t v_sz_4714_, size_t v_i_4715_, lean_object* v_bs_4716_){
_start:
{
uint8_t v___x_4717_; 
v___x_4717_ = lean_usize_dec_lt(v_i_4715_, v_sz_4714_);
if (v___x_4717_ == 0)
{
return v_bs_4716_;
}
else
{
lean_object* v_v_4718_; lean_object* v_fst_4719_; lean_object* v___x_4720_; lean_object* v_bs_x27_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; size_t v___x_4725_; size_t v___x_4726_; lean_object* v___x_4727_; 
v_v_4718_ = lean_array_uget_borrowed(v_bs_4716_, v_i_4715_);
v_fst_4719_ = lean_ctor_get(v_v_4718_, 0);
lean_inc(v_fst_4719_);
v___x_4720_ = lean_unsigned_to_nat(0u);
v_bs_x27_4721_ = lean_array_uset(v_bs_4716_, v_i_4715_, v___x_4720_);
v___x_4722_ = l_Lean_mkCasesOnName(v_fst_4719_);
v___x_4723_ = ((lean_object*)(l_Lean_Elab_ComputedFields_overrideCasesOn___closed__1));
v___x_4724_ = l_Lean_Name_append(v___x_4722_, v___x_4723_);
v___x_4725_ = ((size_t)1ULL);
v___x_4726_ = lean_usize_add(v_i_4715_, v___x_4725_);
v___x_4727_ = lean_array_uset(v_bs_x27_4721_, v_i_4715_, v___x_4724_);
v_i_4715_ = v___x_4726_;
v_bs_4716_ = v___x_4727_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5___boxed(lean_object* v_sz_4729_, lean_object* v_i_4730_, lean_object* v_bs_4731_){
_start:
{
size_t v_sz_boxed_4732_; size_t v_i_boxed_4733_; lean_object* v_res_4734_; 
v_sz_boxed_4732_ = lean_unbox_usize(v_sz_4729_);
lean_dec(v_sz_4729_);
v_i_boxed_4733_ = lean_unbox_usize(v_i_4730_);
lean_dec(v_i_4730_);
v_res_4734_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_boxed_4732_, v_i_boxed_4733_, v_bs_4731_);
return v_res_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields(lean_object* v_computedFields_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v___x_4743_; size_t v_sz_4744_; size_t v___x_4745_; lean_object* v___x_4746_; 
v___x_4743_ = lean_box(0);
v_sz_4744_ = lean_array_size(v_computedFields_4737_);
v___x_4745_ = ((size_t)0ULL);
v___x_4746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__4(v_computedFields_4737_, v_sz_4744_, v___x_4745_, v___x_4743_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v___x_4747_; uint8_t v___x_4748_; lean_object* v___x_4749_; 
lean_dec_ref(v___x_4746_);
lean_inc_ref(v_computedFields_4737_);
v___x_4747_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_ComputedFields_setComputedFields_spec__5(v_sz_4744_, v___x_4745_, v_computedFields_4737_);
v___x_4748_ = 1;
v___x_4749_ = l_Lean_compileDecls(v___x_4747_, v___x_4748_, v_a_4740_, v_a_4741_);
if (lean_obj_tag(v___x_4749_) == 0)
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
lean_dec_ref(v___x_4749_);
v___x_4750_ = ((lean_object*)(l_Lean_Elab_ComputedFields_setComputedFields___closed__0));
v___x_4751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__6(v_computedFields_4737_, v_sz_4744_, v___x_4745_, v___x_4750_, v_a_4738_, v_a_4739_, v_a_4740_, v_a_4741_);
lean_dec_ref(v_computedFields_4737_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_object* v_a_4752_; lean_object* v___x_4753_; 
v_a_4752_ = lean_ctor_get(v___x_4751_, 0);
lean_inc(v_a_4752_);
lean_dec_ref(v___x_4751_);
v___x_4753_ = l_Lean_compileDecls(v_a_4752_, v___x_4748_, v_a_4740_, v_a_4741_);
return v___x_4753_;
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4761_; 
v_a_4754_ = lean_ctor_get(v___x_4751_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4751_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4751_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4751_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4759_; 
if (v_isShared_4757_ == 0)
{
v___x_4759_ = v___x_4756_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
}
}
else
{
lean_dec_ref(v_computedFields_4737_);
return v___x_4749_;
}
}
else
{
lean_dec_ref(v_computedFields_4737_);
return v___x_4746_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_ComputedFields_setComputedFields___boxed(lean_object* v_computedFields_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l_Lean_Elab_ComputedFields_setComputedFields(v_computedFields_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(lean_object* v_as_4769_, lean_object* v_as_x27_4770_, lean_object* v_b_4771_, lean_object* v_a_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___redArg(v_as_x27_4770_, v_b_4771_);
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0___boxed(lean_object* v_as_4779_, lean_object* v_as_x27_4780_, lean_object* v_b_4781_, lean_object* v_a_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l_List_forIn_x27_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__0(v_as_4779_, v_as_x27_4780_, v_b_4781_, v_a_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v_as_4779_);
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(lean_object* v_as_4789_, size_t v_sz_4790_, size_t v_i_4791_, lean_object* v_b_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
lean_object* v___x_4798_; 
v___x_4798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___redArg(v_as_4789_, v_sz_4790_, v_i_4791_, v_b_4792_, v___y_4796_);
return v___x_4798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1___boxed(lean_object* v_as_4799_, lean_object* v_sz_4800_, lean_object* v_i_4801_, lean_object* v_b_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
size_t v_sz_boxed_4808_; size_t v_i_boxed_4809_; lean_object* v_res_4810_; 
v_sz_boxed_4808_ = lean_unbox_usize(v_sz_4800_);
lean_dec(v_sz_4800_);
v_i_boxed_4809_ = lean_unbox_usize(v_i_4801_);
lean_dec(v_i_4801_);
v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_ComputedFields_setComputedFields_spec__1(v_as_4799_, v_sz_boxed_4808_, v_i_boxed_4809_, v_b_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec_ref(v_as_4799_);
return v_res_4810_;
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
