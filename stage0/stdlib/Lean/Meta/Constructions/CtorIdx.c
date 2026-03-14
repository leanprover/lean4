// Lean compiler output
// Module: Lean.Meta.Constructions.CtorIdx
// Imports: public import Lean.Meta.Basic import Lean.AddDecl import Lean.Meta.CompletionName import Lean.Linter.Deprecated
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "genCtorIdx"};
static const lean_object* l_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(121, 142, 77, 16, 50, 110, 46, 202)}};
static const lean_object* l_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "generate the `CtorIdx` functions for inductive datatypes"};
static const lean_object* l_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value)}};
static const lean_object* l_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
static const lean_string_object l_mkToCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toCtorIdx"};
static const lean_object* l_mkToCtorIdxName___closed__0 = (const lean_object*)&l_mkToCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_mkToCtorIdxName(lean_object*);
static const lean_string_object l_mkCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_mkCtorIdxName___closed__0 = (const lean_object*)&l_mkCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_mkCtorIdxName(lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdxCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00mkCtorIdx_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00mkCtorIdx_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00mkCtorIdx_spec__13___closed__0 = (const lean_object*)&l_panic___at___00mkCtorIdx_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_mkCtorIdx___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___lam__0___closed__0;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0___boxed(lean_object**);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_mkCtorIdx___lam__1___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__0_value;
static const lean_ctor_object l_mkCtorIdx___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkCtorIdx___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_mkCtorIdx___lam__1___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__1_value;
static const lean_string_object l_mkCtorIdx___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-08-25"};
static const lean_object* l_mkCtorIdx___lam__1___closed__2 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__2_value;
static const lean_ctor_object l_mkCtorIdx___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkCtorIdx___lam__1___closed__2_value)}};
static const lean_object* l_mkCtorIdx___lam__1___closed__3 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_mkCtorIdx___lam__2___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__2___closed__0_value;
static const lean_ctor_object l_mkCtorIdx___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkCtorIdx___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_mkCtorIdx___lam__2___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00mkCtorIdx_spec__3(lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Constructions.CtorIdx"};
static const lean_object* l_mkCtorIdx___lam__3___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__3___closed__0_value;
static const lean_string_object l_mkCtorIdx___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mkCtorIdx"};
static const lean_object* l_mkCtorIdx___lam__3___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__3___closed__1_value;
static lean_once_cell_t l_mkCtorIdx___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___lam__3___closed__2;
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_mkCtorIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to construct `T.ctorIdx` for `"};
static const lean_object* l_mkCtorIdx___closed__0 = (const lean_object*)&l_mkCtorIdx___closed__0_value;
static lean_once_cell_t l_mkCtorIdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___closed__1;
static const lean_string_object l_mkCtorIdx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_mkCtorIdx___closed__2 = (const lean_object*)&l_mkCtorIdx___closed__2_value;
static lean_once_cell_t l_mkCtorIdx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_mkCtorIdx___closed__3;
LEAN_EXPORT lean_object* l_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_mkCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc(v_name_1_);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
lean_inc(v_name_1_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = ((lean_object*)(l_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_49_ = ((lean_object*)(l_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_50_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_48_, v___x_49_, v___x_48_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_mkToCtorIdxName(lean_object* v_indName_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_mkToCtorIdxName___closed__0));
v___x_56_ = l_Lean_Name_str___override(v_indName_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdxName(lean_object* v_indName_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_mkCtorIdxName___closed__0));
v___x_60_ = l_Lean_Name_str___override(v_indName_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdxCore_x3f(lean_object* v_env_61_, lean_object* v_declName_62_){
_start:
{
if (lean_obj_tag(v_declName_62_) == 1)
{
lean_object* v_pre_63_; lean_object* v_str_64_; lean_object* v___x_65_; uint8_t v___x_66_; 
v_pre_63_ = lean_ctor_get(v_declName_62_, 0);
lean_inc(v_pre_63_);
v_str_64_ = lean_ctor_get(v_declName_62_, 1);
lean_inc_ref(v_str_64_);
lean_dec_ref(v_declName_62_);
v___x_65_ = ((lean_object*)(l_mkCtorIdxName___closed__0));
v___x_66_ = lean_string_dec_eq(v_str_64_, v___x_65_);
lean_dec_ref(v_str_64_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; 
lean_dec(v_pre_63_);
lean_dec_ref(v_env_61_);
v___x_67_ = lean_box(0);
return v___x_67_;
}
else
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_isInductiveCore_x3f(v_env_61_, v_pre_63_);
return v___x_68_;
}
}
else
{
lean_object* v___x_69_; 
lean_dec(v_declName_62_);
lean_dec_ref(v_env_61_);
v___x_69_ = lean_box(0);
return v___x_69_;
}
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg(lean_object* v_declName_70_, lean_object* v_a_71_){
_start:
{
lean_object* v___x_73_; lean_object* v_env_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = lean_st_ref_get(v_a_71_);
v_env_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_env_74_);
lean_dec(v___x_73_);
v___x_75_ = l_isCtorIdxCore_x3f(v_env_74_, v_declName_70_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_isCtorIdx_x3f___redArg(v_declName_77_, v_a_78_);
lean_dec(v_a_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f(lean_object* v_declName_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_isCtorIdx_x3f___redArg(v_declName_81_, v_a_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___boxed(lean_object* v_declName_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_isCtorIdx_x3f(v_declName_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_);
lean_dec(v_a_92_);
lean_dec_ref(v_a_91_);
lean_dec(v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00mkCtorIdx_spec__0(lean_object* v_opts_95_, lean_object* v_opt_96_){
_start:
{
lean_object* v_name_97_; lean_object* v_defValue_98_; lean_object* v_map_99_; lean_object* v___x_100_; 
v_name_97_ = lean_ctor_get(v_opt_96_, 0);
v_defValue_98_ = lean_ctor_get(v_opt_96_, 1);
v_map_99_ = lean_ctor_get(v_opts_95_, 0);
v___x_100_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_99_, v_name_97_);
if (lean_obj_tag(v___x_100_) == 0)
{
uint8_t v___x_101_; 
v___x_101_ = lean_unbox(v_defValue_98_);
return v___x_101_;
}
else
{
lean_object* v_val_102_; 
v_val_102_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_val_102_);
lean_dec_ref(v___x_100_);
if (lean_obj_tag(v_val_102_) == 1)
{
uint8_t v_v_103_; 
v_v_103_ = lean_ctor_get_uint8(v_val_102_, 0);
lean_dec_ref(v_val_102_);
return v_v_103_;
}
else
{
uint8_t v___x_104_; 
lean_dec(v_val_102_);
v___x_104_ = lean_unbox(v_defValue_98_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(lean_object* v_opts_105_, lean_object* v_opt_106_){
_start:
{
uint8_t v_res_107_; lean_object* v_r_108_; 
v_res_107_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_opts_105_, v_opt_106_);
lean_dec_ref(v_opt_106_);
lean_dec_ref(v_opts_105_);
v_r_108_ = lean_box(v_res_107_);
return v_r_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(lean_object* v_constName_109_, uint8_t v_skipRealize_110_, lean_object* v___y_111_){
_start:
{
lean_object* v___x_113_; lean_object* v_env_114_; uint8_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_113_ = lean_st_ref_get(v___y_111_);
v_env_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc_ref(v_env_114_);
lean_dec(v___x_113_);
v___x_115_ = l_Lean_Environment_contains(v_env_114_, v_constName_109_, v_skipRealize_110_);
v___x_116_ = lean_box(v___x_115_);
v___x_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_118_, lean_object* v_skipRealize_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
uint8_t v_skipRealize_boxed_122_; lean_object* v_res_123_; 
v_skipRealize_boxed_122_ = lean_unbox(v_skipRealize_119_);
v_res_123_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v_constName_118_, v_skipRealize_boxed_122_, v___y_120_);
lean_dec(v___y_120_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1(lean_object* v_constName_124_, uint8_t v_skipRealize_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v_constName_124_, v_skipRealize_125_, v___y_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(lean_object* v_constName_132_, lean_object* v_skipRealize_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
uint8_t v_skipRealize_boxed_139_; lean_object* v_res_140_; 
v_skipRealize_boxed_139_ = lean_unbox(v_skipRealize_133_);
v_res_140_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1(v_constName_132_, v_skipRealize_boxed_139_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(lean_object* v_k_141_, lean_object* v_b_142_, lean_object* v_c_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_apply_7(v_k_141_, v_b_142_, v_c_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, lean_box(0));
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object* v_k_150_, lean_object* v_b_151_, lean_object* v_c_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(v_k_150_, v_b_151_, v_c_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(lean_object* v_type_159_, lean_object* v_maxFVars_x3f_160_, lean_object* v_k_161_, uint8_t v_cleanupAnnotations_162_, uint8_t v_whnfType_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___f_169_; lean_object* v___x_170_; 
v___f_169_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_169_, 0, v_k_161_);
v___x_170_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_159_, v_maxFVars_x3f_160_, v___f_169_, v_cleanupAnnotations_162_, v_whnfType_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_object* v_a_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_178_; 
v_a_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_178_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_a_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_178_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_176_; 
if (v_isShared_174_ == 0)
{
v___x_176_ = v___x_173_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_171_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_186_; 
v_a_179_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_186_ == 0)
{
v___x_181_ = v___x_170_;
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_dec(v___x_170_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_186_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_182_ == 0)
{
v___x_184_ = v___x_181_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_a_179_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_187_, lean_object* v_maxFVars_x3f_188_, lean_object* v_k_189_, lean_object* v_cleanupAnnotations_190_, lean_object* v_whnfType_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_197_; uint8_t v_whnfType_boxed_198_; lean_object* v_res_199_; 
v_cleanupAnnotations_boxed_197_ = lean_unbox(v_cleanupAnnotations_190_);
v_whnfType_boxed_198_ = lean_unbox(v_whnfType_191_);
v_res_199_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_187_, v_maxFVars_x3f_188_, v_k_189_, v_cleanupAnnotations_boxed_197_, v_whnfType_boxed_198_, v___y_192_, v___y_193_, v___y_194_, v___y_195_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(lean_object* v_00_u03b1_200_, lean_object* v_type_201_, lean_object* v_maxFVars_x3f_202_, lean_object* v_k_203_, uint8_t v_cleanupAnnotations_204_, uint8_t v_whnfType_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_201_, v_maxFVars_x3f_202_, v_k_203_, v_cleanupAnnotations_204_, v_whnfType_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_212_, lean_object* v_type_213_, lean_object* v_maxFVars_x3f_214_, lean_object* v_k_215_, lean_object* v_cleanupAnnotations_216_, lean_object* v_whnfType_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_223_; uint8_t v_whnfType_boxed_224_; lean_object* v_res_225_; 
v_cleanupAnnotations_boxed_223_ = lean_unbox(v_cleanupAnnotations_216_);
v_whnfType_boxed_224_ = lean_unbox(v_whnfType_217_);
v_res_225_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(v_00_u03b1_212_, v_type_213_, v_maxFVars_x3f_214_, v_k_215_, v_cleanupAnnotations_boxed_223_, v_whnfType_boxed_224_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(lean_object* v_name_226_, lean_object* v_levelParams_227_, lean_object* v_type_228_, lean_object* v_value_229_, lean_object* v_hints_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; uint8_t v___y_235_; uint8_t v___y_242_; lean_object* v_env_245_; uint8_t v___x_246_; 
v___x_233_ = lean_st_ref_get(v___y_231_);
v_env_245_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref(v_env_245_);
lean_dec(v___x_233_);
lean_inc_ref(v_env_245_);
v___x_246_ = l_Lean_Environment_hasUnsafe(v_env_245_, v_type_228_);
if (v___x_246_ == 0)
{
uint8_t v___x_247_; 
v___x_247_ = l_Lean_Environment_hasUnsafe(v_env_245_, v_value_229_);
v___y_242_ = v___x_247_;
goto v___jp_241_;
}
else
{
lean_dec_ref(v_env_245_);
v___y_242_ = v___x_246_;
goto v___jp_241_;
}
v___jp_234_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_inc(v_name_226_);
v___x_236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_236_, 0, v_name_226_);
lean_ctor_set(v___x_236_, 1, v_levelParams_227_);
lean_ctor_set(v___x_236_, 2, v_type_228_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_238_, 0, v_name_226_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_239_, 0, v___x_236_);
lean_ctor_set(v___x_239_, 1, v_value_229_);
lean_ctor_set(v___x_239_, 2, v_hints_230_);
lean_ctor_set(v___x_239_, 3, v___x_238_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*4, v___y_235_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
v___jp_241_:
{
if (v___y_242_ == 0)
{
uint8_t v___x_243_; 
v___x_243_ = 1;
v___y_235_ = v___x_243_;
goto v___jp_234_;
}
else
{
uint8_t v___x_244_; 
v___x_244_ = 0;
v___y_235_ = v___x_244_;
goto v___jp_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_248_, lean_object* v_levelParams_249_, lean_object* v_type_250_, lean_object* v_value_251_, lean_object* v_hints_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v_name_248_, v_levelParams_249_, v_type_250_, v_value_251_, v_hints_252_, v___y_253_);
lean_dec(v___y_253_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(lean_object* v_name_256_, lean_object* v_levelParams_257_, lean_object* v_type_258_, lean_object* v_value_259_, lean_object* v_hints_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v_name_256_, v_levelParams_257_, v_type_258_, v_value_259_, v_hints_260_, v___y_264_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___boxed(lean_object* v_name_267_, lean_object* v_levelParams_268_, lean_object* v_type_269_, lean_object* v_value_270_, lean_object* v_hints_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(v_name_267_, v_levelParams_268_, v_type_269_, v_value_270_, v_hints_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13(lean_object* v_msg_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___f_285_; lean_object* v___x_19860__overap_286_; lean_object* v___x_287_; 
v___f_285_ = ((lean_object*)(l_panic___at___00mkCtorIdx_spec__13___closed__0));
v___x_19860__overap_286_ = lean_panic_fn(v___f_285_, v_msg_279_);
v___x_287_ = lean_apply_5(v___x_19860__overap_286_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, lean_box(0));
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13___boxed(lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_panic___at___00mkCtorIdx_spec__13(v_msg_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(lean_object* v___y_295_, uint8_t v_isExporting_296_, lean_object* v___x_297_, lean_object* v___y_298_, lean_object* v___x_299_, lean_object* v_a_x3f_300_){
_start:
{
lean_object* v___x_302_; lean_object* v_env_303_; lean_object* v_nextMacroScope_304_; lean_object* v_ngen_305_; lean_object* v_auxDeclNGen_306_; lean_object* v_traceState_307_; lean_object* v_messages_308_; lean_object* v_infoState_309_; lean_object* v_snapshotTasks_310_; lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_335_; 
v___x_302_ = lean_st_ref_take(v___y_295_);
v_env_303_ = lean_ctor_get(v___x_302_, 0);
v_nextMacroScope_304_ = lean_ctor_get(v___x_302_, 1);
v_ngen_305_ = lean_ctor_get(v___x_302_, 2);
v_auxDeclNGen_306_ = lean_ctor_get(v___x_302_, 3);
v_traceState_307_ = lean_ctor_get(v___x_302_, 4);
v_messages_308_ = lean_ctor_get(v___x_302_, 6);
v_infoState_309_ = lean_ctor_get(v___x_302_, 7);
v_snapshotTasks_310_ = lean_ctor_get(v___x_302_, 8);
v_isSharedCheck_335_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_335_ == 0)
{
lean_object* v_unused_336_; 
v_unused_336_ = lean_ctor_get(v___x_302_, 5);
lean_dec(v_unused_336_);
v___x_312_ = v___x_302_;
v_isShared_313_ = v_isSharedCheck_335_;
goto v_resetjp_311_;
}
else
{
lean_inc(v_snapshotTasks_310_);
lean_inc(v_infoState_309_);
lean_inc(v_messages_308_);
lean_inc(v_traceState_307_);
lean_inc(v_auxDeclNGen_306_);
lean_inc(v_ngen_305_);
lean_inc(v_nextMacroScope_304_);
lean_inc(v_env_303_);
lean_dec(v___x_302_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_335_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_314_ = l_Lean_Environment_setExporting(v_env_303_, v_isExporting_296_);
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 5, v___x_297_);
lean_ctor_set(v___x_312_, 0, v___x_314_);
v___x_316_ = v___x_312_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_314_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_nextMacroScope_304_);
lean_ctor_set(v_reuseFailAlloc_334_, 2, v_ngen_305_);
lean_ctor_set(v_reuseFailAlloc_334_, 3, v_auxDeclNGen_306_);
lean_ctor_set(v_reuseFailAlloc_334_, 4, v_traceState_307_);
lean_ctor_set(v_reuseFailAlloc_334_, 5, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_334_, 6, v_messages_308_);
lean_ctor_set(v_reuseFailAlloc_334_, 7, v_infoState_309_);
lean_ctor_set(v_reuseFailAlloc_334_, 8, v_snapshotTasks_310_);
v___x_316_ = v_reuseFailAlloc_334_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v_mctx_319_; lean_object* v_zetaDeltaFVarIds_320_; lean_object* v_postponed_321_; lean_object* v_diag_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_332_; 
v___x_317_ = lean_st_ref_set(v___y_295_, v___x_316_);
v___x_318_ = lean_st_ref_take(v___y_298_);
v_mctx_319_ = lean_ctor_get(v___x_318_, 0);
v_zetaDeltaFVarIds_320_ = lean_ctor_get(v___x_318_, 2);
v_postponed_321_ = lean_ctor_get(v___x_318_, 3);
v_diag_322_ = lean_ctor_get(v___x_318_, 4);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v___x_318_, 1);
lean_dec(v_unused_333_);
v___x_324_ = v___x_318_;
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_diag_322_);
lean_inc(v_postponed_321_);
lean_inc(v_zetaDeltaFVarIds_320_);
lean_inc(v_mctx_319_);
lean_dec(v___x_318_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_332_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
lean_ctor_set(v___x_324_, 1, v___x_299_);
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_mctx_319_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_331_, 2, v_zetaDeltaFVarIds_320_);
lean_ctor_set(v_reuseFailAlloc_331_, 3, v_postponed_321_);
lean_ctor_set(v_reuseFailAlloc_331_, 4, v_diag_322_);
v___x_327_ = v_reuseFailAlloc_331_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_st_ref_set(v___y_298_, v___x_327_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object* v___y_337_, lean_object* v_isExporting_338_, lean_object* v___x_339_, lean_object* v___y_340_, lean_object* v___x_341_, lean_object* v_a_x3f_342_, lean_object* v___y_343_){
_start:
{
uint8_t v_isExporting_boxed_344_; lean_object* v_res_345_; 
v_isExporting_boxed_344_ = lean_unbox(v_isExporting_338_);
v_res_345_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_337_, v_isExporting_boxed_344_, v___x_339_, v___y_340_, v___x_341_, v_a_x3f_342_);
lean_dec(v_a_x3f_342_);
lean_dec(v___y_340_);
lean_dec(v___y_337_);
return v_res_345_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_346_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0);
v___x_348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_349_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1);
v___x_352_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
lean_ctor_set(v___x_352_, 2, v___x_351_);
lean_ctor_set(v___x_352_, 3, v___x_351_);
lean_ctor_set(v___x_352_, 4, v___x_351_);
lean_ctor_set(v___x_352_, 5, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(lean_object* v_x_353_, uint8_t v_isExporting_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v___x_360_; lean_object* v_env_361_; uint8_t v_isExporting_362_; lean_object* v___x_363_; lean_object* v_env_364_; lean_object* v_nextMacroScope_365_; lean_object* v_ngen_366_; lean_object* v_auxDeclNGen_367_; lean_object* v_traceState_368_; lean_object* v_messages_369_; lean_object* v_infoState_370_; lean_object* v_snapshotTasks_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_425_; 
v___x_360_ = lean_st_ref_get(v___y_358_);
v_env_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc_ref(v_env_361_);
lean_dec(v___x_360_);
v_isExporting_362_ = lean_ctor_get_uint8(v_env_361_, sizeof(void*)*8);
lean_dec_ref(v_env_361_);
v___x_363_ = lean_st_ref_take(v___y_358_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
v_nextMacroScope_365_ = lean_ctor_get(v___x_363_, 1);
v_ngen_366_ = lean_ctor_get(v___x_363_, 2);
v_auxDeclNGen_367_ = lean_ctor_get(v___x_363_, 3);
v_traceState_368_ = lean_ctor_get(v___x_363_, 4);
v_messages_369_ = lean_ctor_get(v___x_363_, 6);
v_infoState_370_ = lean_ctor_get(v___x_363_, 7);
v_snapshotTasks_371_ = lean_ctor_get(v___x_363_, 8);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_425_ == 0)
{
lean_object* v_unused_426_; 
v_unused_426_ = lean_ctor_get(v___x_363_, 5);
lean_dec(v_unused_426_);
v___x_373_ = v___x_363_;
v_isShared_374_ = v_isSharedCheck_425_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_snapshotTasks_371_);
lean_inc(v_infoState_370_);
lean_inc(v_messages_369_);
lean_inc(v_traceState_368_);
lean_inc(v_auxDeclNGen_367_);
lean_inc(v_ngen_366_);
lean_inc(v_nextMacroScope_365_);
lean_inc(v_env_364_);
lean_dec(v___x_363_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_425_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_375_ = l_Lean_Environment_setExporting(v_env_364_, v_isExporting_354_);
v___x_376_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 5, v___x_376_);
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_378_ = v___x_373_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v___x_375_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v_nextMacroScope_365_);
lean_ctor_set(v_reuseFailAlloc_424_, 2, v_ngen_366_);
lean_ctor_set(v_reuseFailAlloc_424_, 3, v_auxDeclNGen_367_);
lean_ctor_set(v_reuseFailAlloc_424_, 4, v_traceState_368_);
lean_ctor_set(v_reuseFailAlloc_424_, 5, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_424_, 6, v_messages_369_);
lean_ctor_set(v_reuseFailAlloc_424_, 7, v_infoState_370_);
lean_ctor_set(v_reuseFailAlloc_424_, 8, v_snapshotTasks_371_);
v___x_378_ = v_reuseFailAlloc_424_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v_mctx_381_; lean_object* v_zetaDeltaFVarIds_382_; lean_object* v_postponed_383_; lean_object* v_diag_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_422_; 
v___x_379_ = lean_st_ref_set(v___y_358_, v___x_378_);
v___x_380_ = lean_st_ref_take(v___y_356_);
v_mctx_381_ = lean_ctor_get(v___x_380_, 0);
v_zetaDeltaFVarIds_382_ = lean_ctor_get(v___x_380_, 2);
v_postponed_383_ = lean_ctor_get(v___x_380_, 3);
v_diag_384_ = lean_ctor_get(v___x_380_, 4);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v___x_380_, 1);
lean_dec(v_unused_423_);
v___x_386_ = v___x_380_;
v_isShared_387_ = v_isSharedCheck_422_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_diag_384_);
lean_inc(v_postponed_383_);
lean_inc(v_zetaDeltaFVarIds_382_);
lean_inc(v_mctx_381_);
lean_dec(v___x_380_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_422_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_390_; 
v___x_388_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v___x_388_);
v___x_390_ = v___x_386_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_mctx_381_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_421_, 2, v_zetaDeltaFVarIds_382_);
lean_ctor_set(v_reuseFailAlloc_421_, 3, v_postponed_383_);
lean_ctor_set(v_reuseFailAlloc_421_, 4, v_diag_384_);
v___x_390_ = v_reuseFailAlloc_421_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v_r_392_; 
v___x_391_ = lean_st_ref_set(v___y_356_, v___x_390_);
lean_inc(v___y_358_);
lean_inc(v___y_356_);
v_r_392_ = lean_apply_5(v_x_353_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, lean_box(0));
if (lean_obj_tag(v_r_392_) == 0)
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_409_; 
v_a_393_ = lean_ctor_get(v_r_392_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v_r_392_);
if (v_isSharedCheck_409_ == 0)
{
v___x_395_ = v_r_392_;
v_isShared_396_ = v_isSharedCheck_409_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v_r_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_409_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
lean_inc(v_a_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set_tag(v___x_395_, 1);
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_393_);
v___x_398_ = v_reuseFailAlloc_408_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v___x_399_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_358_, v_isExporting_362_, v___x_376_, v___y_356_, v___x_388_, v___x_398_);
lean_dec_ref(v___x_398_);
lean_dec(v___y_356_);
lean_dec(v___y_358_);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_406_ == 0)
{
lean_object* v_unused_407_; 
v_unused_407_ = lean_ctor_get(v___x_399_, 0);
lean_dec(v_unused_407_);
v___x_401_ = v___x_399_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_dec(v___x_399_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
lean_ctor_set(v___x_401_, 0, v_a_393_);
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_393_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
else
{
lean_object* v_a_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_419_; 
v_a_410_ = lean_ctor_get(v_r_392_, 0);
lean_inc(v_a_410_);
lean_dec_ref(v_r_392_);
v___x_411_ = lean_box(0);
v___x_412_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_358_, v_isExporting_362_, v___x_376_, v___y_356_, v___x_388_, v___x_411_);
lean_dec(v___y_356_);
lean_dec(v___y_358_);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_412_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v___x_412_, 0);
lean_dec(v_unused_420_);
v___x_414_ = v___x_412_;
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
else
{
lean_dec(v___x_412_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_419_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_417_; 
if (v_isShared_415_ == 0)
{
lean_ctor_set_tag(v___x_414_, 1);
lean_ctor_set(v___x_414_, 0, v_a_410_);
v___x_417_ = v___x_414_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_a_410_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___boxed(lean_object* v_x_427_, lean_object* v_isExporting_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
uint8_t v_isExporting_boxed_434_; lean_object* v_res_435_; 
v_isExporting_boxed_434_ = lean_unbox(v_isExporting_428_);
v_res_435_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v_x_427_, v_isExporting_boxed_434_, v___y_429_, v___y_430_, v___y_431_, v___y_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14(lean_object* v_00_u03b1_436_, lean_object* v_x_437_, uint8_t v_isExporting_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v_x_437_, v_isExporting_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___boxed(lean_object* v_00_u03b1_445_, lean_object* v_x_446_, lean_object* v_isExporting_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
uint8_t v_isExporting_boxed_453_; lean_object* v_res_454_; 
v_isExporting_boxed_453_ = lean_unbox(v_isExporting_447_);
v_res_454_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14(v_00_u03b1_445_, v_x_446_, v_isExporting_boxed_453_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
lean_object* v___x_461_; lean_object* v_env_462_; lean_object* v___x_463_; lean_object* v_mctx_464_; lean_object* v_lctx_465_; lean_object* v_options_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_461_ = lean_st_ref_get(v___y_459_);
v_env_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_env_462_);
lean_dec(v___x_461_);
v___x_463_ = lean_st_ref_get(v___y_457_);
v_mctx_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc_ref(v_mctx_464_);
lean_dec(v___x_463_);
v_lctx_465_ = lean_ctor_get(v___y_456_, 2);
v_options_466_ = lean_ctor_get(v___y_458_, 2);
lean_inc_ref(v_options_466_);
lean_inc_ref(v_lctx_465_);
v___x_467_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_467_, 0, v_env_462_);
lean_ctor_set(v___x_467_, 1, v_mctx_464_);
lean_ctor_set(v___x_467_, 2, v_lctx_465_);
lean_ctor_set(v___x_467_, 3, v_options_466_);
v___x_468_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_msgData_455_);
v___x_469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
lean_dec(v___y_474_);
lean_dec_ref(v___y_473_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v_ref_483_; lean_object* v___x_484_; lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_493_; 
v_ref_483_ = lean_ctor_get(v___y_480_, 5);
v___x_484_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msg_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_493_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_493_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
lean_inc(v_ref_483_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v_ref_483_);
lean_ctor_set(v___x_489_, 1, v_a_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set_tag(v___x_487_, 1);
lean_ctor_set(v___x_487_, 0, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_489_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_500_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_instMonadEST(lean_box(0), lean_box(0));
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_toApplicative_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_575_; 
v___x_512_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0);
v___x_513_ = l_ReaderT_instMonad___redArg(v___x_512_);
v_toApplicative_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v___x_513_, 1);
lean_dec(v_unused_576_);
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_575_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_toApplicative_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_575_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_toFunctor_518_; lean_object* v_toSeq_519_; lean_object* v_toSeqLeft_520_; lean_object* v_toSeqRight_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_573_; 
v_toFunctor_518_ = lean_ctor_get(v_toApplicative_514_, 0);
v_toSeq_519_ = lean_ctor_get(v_toApplicative_514_, 2);
v_toSeqLeft_520_ = lean_ctor_get(v_toApplicative_514_, 3);
v_toSeqRight_521_ = lean_ctor_get(v_toApplicative_514_, 4);
v_isSharedCheck_573_ = !lean_is_exclusive(v_toApplicative_514_);
if (v_isSharedCheck_573_ == 0)
{
lean_object* v_unused_574_; 
v_unused_574_ = lean_ctor_get(v_toApplicative_514_, 1);
lean_dec(v_unused_574_);
v___x_523_ = v_toApplicative_514_;
v_isShared_524_ = v_isSharedCheck_573_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_toSeqRight_521_);
lean_inc(v_toSeqLeft_520_);
lean_inc(v_toSeq_519_);
lean_inc(v_toFunctor_518_);
lean_dec(v_toApplicative_514_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_573_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___f_525_; lean_object* v___f_526_; lean_object* v___f_527_; lean_object* v___f_528_; lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___f_531_; lean_object* v___f_532_; lean_object* v___x_534_; 
v___f_525_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1));
v___f_526_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_518_);
v___f_527_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_527_, 0, v_toFunctor_518_);
v___f_528_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_528_, 0, v_toFunctor_518_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v___f_527_);
lean_ctor_set(v___x_529_, 1, v___f_528_);
v___f_530_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_530_, 0, v_toSeqRight_521_);
v___f_531_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_531_, 0, v_toSeqLeft_520_);
v___f_532_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_532_, 0, v_toSeq_519_);
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 4, v___f_530_);
lean_ctor_set(v___x_523_, 3, v___f_531_);
lean_ctor_set(v___x_523_, 2, v___f_532_);
lean_ctor_set(v___x_523_, 1, v___f_525_);
lean_ctor_set(v___x_523_, 0, v___x_529_);
v___x_534_ = v___x_523_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v___f_525_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v___f_532_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v___f_531_);
lean_ctor_set(v_reuseFailAlloc_572_, 4, v___f_530_);
v___x_534_ = v_reuseFailAlloc_572_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
lean_object* v___x_536_; 
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v___f_526_);
lean_ctor_set(v___x_516_, 0, v___x_534_);
v___x_536_ = v___x_516_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___f_526_);
v___x_536_ = v_reuseFailAlloc_571_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; lean_object* v_toApplicative_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_569_; 
v___x_537_ = l_ReaderT_instMonad___redArg(v___x_536_);
v_toApplicative_538_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_569_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v___x_537_, 1);
lean_dec(v_unused_570_);
v___x_540_ = v___x_537_;
v_isShared_541_ = v_isSharedCheck_569_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_toApplicative_538_);
lean_dec(v___x_537_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_569_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v_toFunctor_542_; lean_object* v_toSeq_543_; lean_object* v_toSeqLeft_544_; lean_object* v_toSeqRight_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_567_; 
v_toFunctor_542_ = lean_ctor_get(v_toApplicative_538_, 0);
v_toSeq_543_ = lean_ctor_get(v_toApplicative_538_, 2);
v_toSeqLeft_544_ = lean_ctor_get(v_toApplicative_538_, 3);
v_toSeqRight_545_ = lean_ctor_get(v_toApplicative_538_, 4);
v_isSharedCheck_567_ = !lean_is_exclusive(v_toApplicative_538_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; 
v_unused_568_ = lean_ctor_get(v_toApplicative_538_, 1);
lean_dec(v_unused_568_);
v___x_547_ = v_toApplicative_538_;
v_isShared_548_ = v_isSharedCheck_567_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_toSeqRight_545_);
lean_inc(v_toSeqLeft_544_);
lean_inc(v_toSeq_543_);
lean_inc(v_toFunctor_542_);
lean_dec(v_toApplicative_538_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_567_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___f_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___f_552_; lean_object* v___x_553_; lean_object* v___f_554_; lean_object* v___f_555_; lean_object* v___f_556_; lean_object* v___x_558_; 
v___f_549_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3));
v___f_550_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_542_);
v___f_551_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_551_, 0, v_toFunctor_542_);
v___f_552_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_552_, 0, v_toFunctor_542_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___f_551_);
lean_ctor_set(v___x_553_, 1, v___f_552_);
v___f_554_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_554_, 0, v_toSeqRight_545_);
v___f_555_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_555_, 0, v_toSeqLeft_544_);
v___f_556_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_556_, 0, v_toSeq_543_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 4, v___f_554_);
lean_ctor_set(v___x_547_, 3, v___f_555_);
lean_ctor_set(v___x_547_, 2, v___f_556_);
lean_ctor_set(v___x_547_, 1, v___f_549_);
lean_ctor_set(v___x_547_, 0, v___x_553_);
v___x_558_ = v___x_547_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_553_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___f_549_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v___f_556_);
lean_ctor_set(v_reuseFailAlloc_566_, 3, v___f_555_);
lean_ctor_set(v_reuseFailAlloc_566_, 4, v___f_554_);
v___x_558_ = v_reuseFailAlloc_566_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_560_; 
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 1, v___f_550_);
lean_ctor_set(v___x_540_, 0, v___x_558_);
v___x_560_ = v___x_540_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_558_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___f_550_);
v___x_560_ = v_reuseFailAlloc_565_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_23691__overap_563_; lean_object* v___x_564_; 
v___x_561_ = lean_box(0);
v___x_562_ = l_instInhabitedOfMonad___redArg(v___x_560_, v___x_561_);
v___x_23691__overap_563_ = lean_panic_fn(v___x_562_, v_msg_506_);
v___x_564_ = lean_apply_5(v___x_23691__overap_563_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, lean_box(0));
return v___x_564_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v_msg_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
return v_res_583_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_593_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_594_ = lean_unsigned_to_nat(11u);
v___x_595_ = lean_unsigned_to_nat(122u);
v___x_596_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5));
v___x_597_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4));
v___x_598_ = l_mkPanicMessageWithDecl(v___x_597_, v___x_596_, v___x_595_, v___x_594_, v___x_593_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(lean_object* v_constName_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
lean_object* v___x_613_; lean_object* v_env_614_; uint8_t v___x_615_; lean_object* v___x_616_; 
v___x_613_ = lean_st_ref_get(v___y_603_);
v_env_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc_ref(v_env_614_);
lean_dec(v___x_613_);
v___x_615_ = 0;
lean_inc(v_constName_599_);
v___x_616_ = l_Lean_Environment_findAsync_x3f(v_env_614_, v_constName_599_, v___x_615_);
if (lean_obj_tag(v___x_616_) == 1)
{
lean_object* v_val_617_; uint8_t v_kind_618_; 
v_val_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_val_617_);
lean_dec_ref(v___x_616_);
v_kind_618_ = lean_ctor_get_uint8(v_val_617_, sizeof(void*)*3);
if (v_kind_618_ == 6)
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_617_);
if (lean_obj_tag(v___x_619_) == 6)
{
lean_object* v_val_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v_constName_599_);
v_val_620_ = lean_ctor_get(v___x_619_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_619_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_val_620_);
lean_dec(v___x_619_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set_tag(v___x_622_, 0);
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_val_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; 
lean_dec_ref(v___x_619_);
v___x_628_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7);
lean_inc(v___y_603_);
lean_inc_ref(v___y_602_);
lean_inc(v___y_601_);
lean_inc_ref(v___y_600_);
v___x_629_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v___x_628_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_a_630_; lean_object* v___x_632_; uint8_t v_isShared_633_; uint8_t v_isSharedCheck_638_; 
v_a_630_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_638_ == 0)
{
v___x_632_ = v___x_629_;
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
else
{
lean_inc(v_a_630_);
lean_dec(v___x_629_);
v___x_632_ = lean_box(0);
v_isShared_633_ = v_isSharedCheck_638_;
goto v_resetjp_631_;
}
v_resetjp_631_:
{
if (lean_obj_tag(v_a_630_) == 0)
{
lean_del_object(v___x_632_);
goto v___jp_605_;
}
else
{
lean_object* v_val_634_; lean_object* v___x_636_; 
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v_constName_599_);
v_val_634_ = lean_ctor_get(v_a_630_, 0);
lean_inc(v_val_634_);
lean_dec_ref(v_a_630_);
if (v_isShared_633_ == 0)
{
lean_ctor_set(v___x_632_, 0, v_val_634_);
v___x_636_ = v___x_632_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_val_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
}
}
else
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_646_; 
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v_constName_599_);
v_a_639_ = lean_ctor_get(v___x_629_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_629_);
if (v_isSharedCheck_646_ == 0)
{
v___x_641_ = v___x_629_;
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_629_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_646_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_644_; 
if (v_isShared_642_ == 0)
{
v___x_644_ = v___x_641_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_a_639_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
}
}
else
{
lean_dec(v_val_617_);
goto v___jp_605_;
}
}
else
{
lean_dec(v___x_616_);
goto v___jp_605_;
}
v___jp_605_:
{
lean_object* v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_606_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_607_ = 0;
v___x_608_ = l_Lean_MessageData_ofConstName(v_constName_599_, v___x_607_);
v___x_609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_606_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_611_, v___y_600_, v___y_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(lean_object* v_constName_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_constName_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_654_, uint8_t v___x_655_, uint8_t v___x_656_, uint8_t v___x_657_, lean_object* v_ys_658_, lean_object* v_x_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = l_Lean_mkRawNatLit(v_cidx_654_);
v___x_666_ = l_Lean_Meta_mkLambdaFVars(v_ys_658_, v___x_665_, v___x_655_, v___x_656_, v___x_655_, v___x_656_, v___x_657_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v_ys_671_, lean_object* v_x_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
uint8_t v___x_28484__boxed_678_; uint8_t v___x_28485__boxed_679_; uint8_t v___x_28486__boxed_680_; lean_object* v_res_681_; 
v___x_28484__boxed_678_ = lean_unbox(v___x_668_);
v___x_28485__boxed_679_ = lean_unbox(v___x_669_);
v___x_28486__boxed_680_ = lean_unbox(v___x_670_);
v_res_681_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(v_cidx_667_, v___x_28484__boxed_678_, v___x_28485__boxed_679_, v___x_28486__boxed_680_, v_ys_671_, v_x_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec_ref(v_x_672_);
lean_dec_ref(v_ys_671_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(uint8_t v___x_682_, lean_object* v___x_683_, lean_object* v_as_x27_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
if (lean_obj_tag(v_as_x27_684_) == 0)
{
lean_object* v___x_691_; 
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_b_685_);
return v___x_691_;
}
else
{
lean_object* v_head_692_; lean_object* v_tail_693_; lean_object* v___x_694_; 
v_head_692_ = lean_ctor_get(v_as_x27_684_, 0);
lean_inc(v_head_692_);
v_tail_693_ = lean_ctor_get(v_as_x27_684_, 1);
lean_inc(v_tail_693_);
lean_dec_ref(v_as_x27_684_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
v___x_694_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_head_692_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v_toConstantVal_696_; lean_object* v_cidx_697_; lean_object* v_numFields_698_; lean_object* v_type_699_; lean_object* v___x_700_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v_toConstantVal_696_ = lean_ctor_get(v_a_695_, 0);
lean_inc_ref(v_toConstantVal_696_);
v_cidx_697_ = lean_ctor_get(v_a_695_, 2);
lean_inc(v_cidx_697_);
v_numFields_698_ = lean_ctor_get(v_a_695_, 4);
lean_inc(v_numFields_698_);
lean_dec(v_a_695_);
v_type_699_ = lean_ctor_get(v_toConstantVal_696_, 2);
lean_inc_ref(v_type_699_);
lean_dec_ref(v_toConstantVal_696_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
v___x_700_ = l_Lean_Meta_instantiateForall(v_type_699_, v___x_683_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_718_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_718_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_718_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_718_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
uint8_t v___x_705_; uint8_t v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___f_710_; lean_object* v___x_712_; 
v___x_705_ = 0;
v___x_706_ = 1;
v___x_707_ = lean_box(v___x_705_);
v___x_708_ = lean_box(v___x_682_);
v___x_709_ = lean_box(v___x_706_);
v___f_710_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_710_, 0, v_cidx_697_);
lean_closure_set(v___f_710_, 1, v___x_707_);
lean_closure_set(v___f_710_, 2, v___x_708_);
lean_closure_set(v___f_710_, 3, v___x_709_);
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 1);
lean_ctor_set(v___x_703_, 0, v_numFields_698_);
v___x_712_ = v___x_703_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_numFields_698_);
v___x_712_ = v_reuseFailAlloc_717_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; 
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
v___x_713_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_a_701_, v___x_712_, v___f_710_, v___x_705_, v___x_705_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_715_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref(v___x_713_);
v___x_715_ = l_Lean_Expr_app___override(v_b_685_, v_a_714_);
v_as_x27_684_ = v_tail_693_;
v_b_685_ = v___x_715_;
goto _start;
}
else
{
lean_dec(v_tail_693_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_b_685_);
return v___x_713_;
}
}
}
}
else
{
lean_dec(v_numFields_698_);
lean_dec(v_cidx_697_);
lean_dec(v_tail_693_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_b_685_);
return v___x_700_;
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_tail_693_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec_ref(v_b_685_);
v_a_719_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_694_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_694_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_727_, lean_object* v___x_728_, lean_object* v_as_x27_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v___x_28515__boxed_736_; lean_object* v_res_737_; 
v___x_28515__boxed_736_ = lean_unbox(v___x_727_);
v_res_737_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_28515__boxed_736_, v___x_728_, v_as_x27_729_, v_b_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec_ref(v___x_728_);
return v_res_737_;
}
}
static lean_object* _init_l_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_box(0);
v___x_739_ = l_Lean_Level_succ___override(v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0(lean_object* v_xs_740_, uint8_t v___x_741_, uint8_t v___x_742_, uint8_t v___x_743_, lean_object* v_val_744_, lean_object* v___x_745_, lean_object* v___x_746_, lean_object* v___x_747_, lean_object* v___x_748_, lean_object* v___x_749_, lean_object* v_ctors_750_, lean_object* v___x_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_){
_start:
{
lean_object* v_value_759_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v___x_762_ = l_Lean_InductiveVal_numCtors(v_val_744_);
v___x_763_ = lean_unsigned_to_nat(1u);
v___x_764_ = lean_nat_dec_eq(v___x_762_, v___x_763_);
lean_dec(v___x_762_);
if (v___x_764_ == 0)
{
lean_object* v___x_765_; lean_object* v___x_766_; 
lean_dec(v___x_751_);
lean_inc_ref(v_x_752_);
lean_inc_ref(v___x_745_);
v___x_765_ = lean_array_push(v___x_745_, v_x_752_);
v___x_766_ = l_Lean_Meta_mkLambdaFVars(v___x_765_, v___x_746_, v___x_741_, v___x_742_, v___x_741_, v___x_742_, v___x_743_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec_ref(v___x_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
lean_dec_ref(v___x_766_);
v___x_768_ = lean_obj_once(&l_mkCtorIdx___lam__0___closed__0, &l_mkCtorIdx___lam__0___closed__0_once, _init_l_mkCtorIdx___lam__0___closed__0);
v___x_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_747_);
v___x_770_ = l_Lean_mkConst(v___x_748_, v___x_769_);
v___x_771_ = l_Lean_mkAppN(v___x_770_, v___x_749_);
v___x_772_ = l_Lean_Expr_app___override(v___x_771_, v_a_767_);
v___x_773_ = l_Lean_mkAppN(v___x_772_, v___x_745_);
lean_dec_ref(v___x_745_);
lean_inc_ref(v_x_752_);
v___x_774_ = l_Lean_Expr_app___override(v___x_773_, v_x_752_);
lean_inc(v___y_756_);
lean_inc_ref(v___y_755_);
lean_inc(v___y_754_);
lean_inc_ref(v___y_753_);
v___x_775_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_742_, v___x_749_, v_ctors_750_, v___x_774_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref(v___x_775_);
v_value_759_ = v_a_776_;
goto v___jp_758_;
}
else
{
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec_ref(v_x_752_);
lean_dec_ref(v_xs_740_);
return v___x_775_;
}
}
else
{
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec_ref(v_x_752_);
lean_dec(v_ctors_750_);
lean_dec(v___x_748_);
lean_dec(v___x_747_);
lean_dec_ref(v___x_745_);
lean_dec_ref(v_xs_740_);
return v___x_766_;
}
}
else
{
lean_object* v___x_777_; 
lean_dec(v_ctors_750_);
lean_dec(v___x_748_);
lean_dec(v___x_747_);
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_745_);
v___x_777_ = l_Lean_mkRawNatLit(v___x_751_);
v_value_759_ = v___x_777_;
goto v___jp_758_;
}
v___jp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_array_push(v_xs_740_, v_x_752_);
v___x_761_ = l_Lean_Meta_mkLambdaFVars(v___x_760_, v_value_759_, v___x_741_, v___x_742_, v___x_741_, v___x_742_, v___x_743_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
lean_dec(v___y_756_);
lean_dec_ref(v___y_755_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec_ref(v___x_760_);
return v___x_761_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_778_ = _args[0];
lean_object* v___x_779_ = _args[1];
lean_object* v___x_780_ = _args[2];
lean_object* v___x_781_ = _args[3];
lean_object* v_val_782_ = _args[4];
lean_object* v___x_783_ = _args[5];
lean_object* v___x_784_ = _args[6];
lean_object* v___x_785_ = _args[7];
lean_object* v___x_786_ = _args[8];
lean_object* v___x_787_ = _args[9];
lean_object* v_ctors_788_ = _args[10];
lean_object* v___x_789_ = _args[11];
lean_object* v_x_790_ = _args[12];
lean_object* v___y_791_ = _args[13];
lean_object* v___y_792_ = _args[14];
lean_object* v___y_793_ = _args[15];
lean_object* v___y_794_ = _args[16];
lean_object* v___y_795_ = _args[17];
_start:
{
uint8_t v___x_28606__boxed_796_; uint8_t v___x_28607__boxed_797_; uint8_t v___x_28608__boxed_798_; lean_object* v_res_799_; 
v___x_28606__boxed_796_ = lean_unbox(v___x_779_);
v___x_28607__boxed_797_ = lean_unbox(v___x_780_);
v___x_28608__boxed_798_ = lean_unbox(v___x_781_);
v_res_799_ = l_mkCtorIdx___lam__0(v_xs_778_, v___x_28606__boxed_796_, v___x_28607__boxed_797_, v___x_28608__boxed_798_, v_val_782_, v___x_783_, v___x_784_, v___x_785_, v___x_786_, v___x_787_, v_ctors_788_, v___x_789_, v_x_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec_ref(v___x_787_);
lean_dec_ref(v_val_782_);
return v_res_799_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_800_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
v___x_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
return v___x_802_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_803_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_805_, 0, v___x_804_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
lean_ctor_set(v___x_805_, 2, v___x_804_);
lean_ctor_set(v___x_805_, 3, v___x_803_);
lean_ctor_set(v___x_805_, 4, v___x_803_);
lean_ctor_set(v___x_805_, 5, v___x_803_);
lean_ctor_set(v___x_805_, 6, v___x_803_);
lean_ctor_set(v___x_805_, 7, v___x_803_);
lean_ctor_set(v___x_805_, 8, v___x_803_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_unsigned_to_nat(32u);
v___x_807_ = lean_mk_empty_array_with_capacity(v___x_806_);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_809_ = ((size_t)5ULL);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = lean_unsigned_to_nat(32u);
v___x_812_ = lean_mk_empty_array_with_capacity(v___x_811_);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
v___x_814_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
lean_ctor_set(v___x_814_, 2, v___x_810_);
lean_ctor_set(v___x_814_, 3, v___x_810_);
lean_ctor_set_usize(v___x_814_, 4, v___x_809_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_815_ = lean_box(1);
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
v___x_817_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___x_816_);
lean_ctor_set(v___x_818_, 2, v___x_815_);
return v___x_818_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6));
v___x_821_ = l_Lean_stringToMessageData(v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8));
v___x_824_ = l_Lean_stringToMessageData(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10));
v___x_827_ = l_Lean_stringToMessageData(v___x_826_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12));
v___x_830_ = l_Lean_stringToMessageData(v___x_829_);
return v___x_830_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_832_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14));
v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
return v___x_833_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16));
v___x_836_ = l_Lean_stringToMessageData(v___x_835_);
return v___x_836_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18));
v___x_839_ = l_Lean_stringToMessageData(v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object* v_msg_840_, lean_object* v_declHint_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; lean_object* v_env_845_; uint8_t v___x_846_; 
v___x_844_ = lean_st_ref_get(v___y_842_);
v_env_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc_ref(v_env_845_);
lean_dec(v___x_844_);
v___x_846_ = l_Lean_Name_isAnonymous(v_declHint_841_);
if (v___x_846_ == 0)
{
uint8_t v_isExporting_847_; 
v_isExporting_847_ = lean_ctor_get_uint8(v_env_845_, sizeof(void*)*8);
if (v_isExporting_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec_ref(v_env_845_);
lean_dec(v_declHint_841_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_msg_840_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; uint8_t v___x_850_; 
lean_inc_ref(v_env_845_);
v___x_849_ = l_Lean_Environment_setExporting(v_env_845_, v___x_846_);
lean_inc(v_declHint_841_);
lean_inc_ref(v___x_849_);
v___x_850_ = l_Lean_Environment_contains(v___x_849_, v_declHint_841_, v_isExporting_847_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v___x_849_);
lean_dec_ref(v_env_845_);
lean_dec(v_declHint_841_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_msg_840_);
return v___x_851_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v_c_857_; lean_object* v___x_858_; 
v___x_852_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
v___x_853_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
v___x_854_ = l_Lean_Options_empty;
v___x_855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_855_, 0, v___x_849_);
lean_ctor_set(v___x_855_, 1, v___x_852_);
lean_ctor_set(v___x_855_, 2, v___x_853_);
lean_ctor_set(v___x_855_, 3, v___x_854_);
lean_inc(v_declHint_841_);
v___x_856_ = l_Lean_MessageData_ofConstName(v_declHint_841_, v___x_846_);
v_c_857_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_857_, 0, v___x_855_);
lean_ctor_set(v_c_857_, 1, v___x_856_);
v___x_858_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_845_, v_declHint_841_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec_ref(v_env_845_);
lean_dec(v_declHint_841_);
v___x_859_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_c_857_);
v___x_861_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
v___x_862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_860_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
v___x_863_ = l_Lean_MessageData_note(v___x_862_);
v___x_864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_864_, 0, v_msg_840_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
return v___x_865_;
}
else
{
lean_object* v_val_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_901_; 
v_val_866_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_901_ == 0)
{
v___x_868_ = v___x_858_;
v_isShared_869_ = v_isSharedCheck_901_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_val_866_);
lean_dec(v___x_858_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_901_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v_mod_873_; uint8_t v___x_874_; 
v___x_870_ = lean_box(0);
v___x_871_ = l_Lean_Environment_header(v_env_845_);
lean_dec_ref(v_env_845_);
v___x_872_ = l_Lean_EnvironmentHeader_moduleNames(v___x_871_);
v_mod_873_ = lean_array_get(v___x_870_, v___x_872_, v_val_866_);
lean_dec(v_val_866_);
lean_dec_ref(v___x_872_);
v___x_874_ = l_Lean_isPrivateName(v_declHint_841_);
lean_dec(v_declHint_841_);
if (v___x_874_ == 0)
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_875_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_875_);
lean_ctor_set(v___x_876_, 1, v_c_857_);
v___x_877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_MessageData_ofName(v_mod_873_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_878_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
v___x_881_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
v___x_883_ = l_Lean_MessageData_note(v___x_882_);
v___x_884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_884_, 0, v_msg_840_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 0);
lean_ctor_set(v___x_868_, 0, v___x_884_);
v___x_886_ = v___x_868_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
else
{
lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_888_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
lean_ctor_set(v___x_889_, 1, v_c_857_);
v___x_890_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_MessageData_ofName(v_mod_873_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v___x_891_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
v___x_894_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_893_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_Lean_MessageData_note(v___x_895_);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v_msg_840_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
if (v_isShared_869_ == 0)
{
lean_ctor_set_tag(v___x_868_, 0);
lean_ctor_set(v___x_868_, 0, v___x_897_);
v___x_899_ = v___x_868_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_902_; 
lean_dec_ref(v_env_845_);
lean_dec(v_declHint_841_);
v___x_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_902_, 0, v_msg_840_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object* v_msg_903_, lean_object* v_declHint_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_903_, v_declHint_904_, v___y_905_);
lean_dec(v___y_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object* v_msg_908_, lean_object* v_declHint_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_925_; 
v___x_915_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_908_, v_declHint_909_, v___y_913_);
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_925_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_925_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_923_; 
v___x_920_ = l_Lean_unknownIdentifierMessageTag;
v___x_921_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
lean_ctor_set(v___x_921_, 1, v_a_916_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_921_);
v___x_923_ = v___x_918_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v___x_921_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object* v_msg_926_, lean_object* v_declHint_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_926_, v_declHint_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object* v_ref_934_, lean_object* v_msg_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_fileName_941_; lean_object* v_fileMap_942_; lean_object* v_options_943_; lean_object* v_currRecDepth_944_; lean_object* v_maxRecDepth_945_; lean_object* v_ref_946_; lean_object* v_currNamespace_947_; lean_object* v_openDecls_948_; lean_object* v_initHeartbeats_949_; lean_object* v_maxHeartbeats_950_; lean_object* v_quotContext_951_; lean_object* v_currMacroScope_952_; uint8_t v_diag_953_; lean_object* v_cancelTk_x3f_954_; uint8_t v_suppressElabErrors_955_; lean_object* v_inheritedTraceOptions_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
v_fileName_941_ = lean_ctor_get(v___y_938_, 0);
v_fileMap_942_ = lean_ctor_get(v___y_938_, 1);
v_options_943_ = lean_ctor_get(v___y_938_, 2);
v_currRecDepth_944_ = lean_ctor_get(v___y_938_, 3);
v_maxRecDepth_945_ = lean_ctor_get(v___y_938_, 4);
v_ref_946_ = lean_ctor_get(v___y_938_, 5);
v_currNamespace_947_ = lean_ctor_get(v___y_938_, 6);
v_openDecls_948_ = lean_ctor_get(v___y_938_, 7);
v_initHeartbeats_949_ = lean_ctor_get(v___y_938_, 8);
v_maxHeartbeats_950_ = lean_ctor_get(v___y_938_, 9);
v_quotContext_951_ = lean_ctor_get(v___y_938_, 10);
v_currMacroScope_952_ = lean_ctor_get(v___y_938_, 11);
v_diag_953_ = lean_ctor_get_uint8(v___y_938_, sizeof(void*)*14);
v_cancelTk_x3f_954_ = lean_ctor_get(v___y_938_, 12);
v_suppressElabErrors_955_ = lean_ctor_get_uint8(v___y_938_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_956_ = lean_ctor_get(v___y_938_, 13);
v_isSharedCheck_965_ = !lean_is_exclusive(v___y_938_);
if (v_isSharedCheck_965_ == 0)
{
v___x_958_ = v___y_938_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_inheritedTraceOptions_956_);
lean_inc(v_cancelTk_x3f_954_);
lean_inc(v_currMacroScope_952_);
lean_inc(v_quotContext_951_);
lean_inc(v_maxHeartbeats_950_);
lean_inc(v_initHeartbeats_949_);
lean_inc(v_openDecls_948_);
lean_inc(v_currNamespace_947_);
lean_inc(v_ref_946_);
lean_inc(v_maxRecDepth_945_);
lean_inc(v_currRecDepth_944_);
lean_inc(v_options_943_);
lean_inc(v_fileMap_942_);
lean_inc(v_fileName_941_);
lean_dec(v___y_938_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v_ref_960_; lean_object* v___x_962_; 
v_ref_960_ = l_Lean_replaceRef(v_ref_934_, v_ref_946_);
lean_dec(v_ref_946_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 5, v_ref_960_);
v___x_962_ = v___x_958_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_fileName_941_);
lean_ctor_set(v_reuseFailAlloc_964_, 1, v_fileMap_942_);
lean_ctor_set(v_reuseFailAlloc_964_, 2, v_options_943_);
lean_ctor_set(v_reuseFailAlloc_964_, 3, v_currRecDepth_944_);
lean_ctor_set(v_reuseFailAlloc_964_, 4, v_maxRecDepth_945_);
lean_ctor_set(v_reuseFailAlloc_964_, 5, v_ref_960_);
lean_ctor_set(v_reuseFailAlloc_964_, 6, v_currNamespace_947_);
lean_ctor_set(v_reuseFailAlloc_964_, 7, v_openDecls_948_);
lean_ctor_set(v_reuseFailAlloc_964_, 8, v_initHeartbeats_949_);
lean_ctor_set(v_reuseFailAlloc_964_, 9, v_maxHeartbeats_950_);
lean_ctor_set(v_reuseFailAlloc_964_, 10, v_quotContext_951_);
lean_ctor_set(v_reuseFailAlloc_964_, 11, v_currMacroScope_952_);
lean_ctor_set(v_reuseFailAlloc_964_, 12, v_cancelTk_x3f_954_);
lean_ctor_set(v_reuseFailAlloc_964_, 13, v_inheritedTraceOptions_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_964_, sizeof(void*)*14, v_diag_953_);
lean_ctor_set_uint8(v_reuseFailAlloc_964_, sizeof(void*)*14 + 1, v_suppressElabErrors_955_);
v___x_962_ = v_reuseFailAlloc_964_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; 
v___x_963_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_935_, v___y_936_, v___y_937_, v___x_962_, v___y_939_);
lean_dec_ref(v___x_962_);
return v___x_963_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object* v_ref_966_, lean_object* v_msg_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_966_, v_msg_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v_ref_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object* v_ref_974_, lean_object* v_msg_975_, lean_object* v_declHint_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; lean_object* v_a_983_; lean_object* v___x_984_; 
v___x_982_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_975_, v_declHint_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref(v___x_982_);
v___x_984_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_974_, v_a_983_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object* v_ref_985_, lean_object* v_msg_986_, lean_object* v_declHint_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_985_, v_msg_986_, v_declHint_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
lean_dec(v___y_991_);
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v_ref_985_);
return v_res_993_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_997_, lean_object* v_constName_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1004_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1005_ = 0;
lean_inc(v_constName_998_);
v___x_1006_ = l_Lean_MessageData_ofConstName(v_constName_998_, v___x_1005_);
v___x_1007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1004_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_1009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_997_, v___x_1009_, v_constName_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
return v___x_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1011_, lean_object* v_constName_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1011_, v_constName_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v_ref_1011_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_ref_1025_; lean_object* v___x_1026_; 
v_ref_1025_ = lean_ctor_get(v___y_1022_, 5);
lean_inc(v_ref_1025_);
v___x_1026_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1025_, v_constName_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v_ref_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(lean_object* v_constName_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___x_1040_; lean_object* v_env_1041_; uint8_t v___x_1042_; lean_object* v___x_1043_; 
v___x_1040_ = lean_st_ref_get(v___y_1038_);
v_env_1041_ = lean_ctor_get(v___x_1040_, 0);
lean_inc_ref(v_env_1041_);
lean_dec(v___x_1040_);
v___x_1042_ = 0;
lean_inc(v_constName_1034_);
v___x_1043_ = l_Lean_Environment_find_x3f(v_env_1041_, v_constName_1034_, v___x_1042_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_);
return v___x_1044_;
}
else
{
lean_object* v_val_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v___y_1037_);
lean_dec(v_constName_1034_);
v_val_1045_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_1043_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_val_1045_);
lean_dec(v___x_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set_tag(v___x_1047_, 0);
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_val_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(lean_object* v_constName_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_constName_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(uint8_t v___x_1060_, lean_object* v_x_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
if (lean_obj_tag(v_x_1061_) == 0)
{
uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
lean_dec_ref(v___y_1064_);
v___x_1067_ = 1;
v___x_1068_ = lean_box(v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
else
{
lean_object* v_head_1070_; lean_object* v_tail_1071_; lean_object* v___x_1072_; 
v_head_1070_ = lean_ctor_get(v_x_1061_, 0);
lean_inc(v_head_1070_);
v_tail_1071_ = lean_ctor_get(v_x_1061_, 1);
lean_inc(v_tail_1071_);
lean_dec_ref(v_x_1061_);
lean_inc_ref(v___y_1064_);
v___x_1072_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_head_1070_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1093_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1093_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1093_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___y_1078_; uint8_t v_a_1079_; 
if (lean_obj_tag(v_a_1073_) == 6)
{
lean_object* v_val_1081_; lean_object* v_numFields_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
v_val_1081_ = lean_ctor_get(v_a_1073_, 0);
lean_inc_ref(v_val_1081_);
lean_dec_ref(v_a_1073_);
v_numFields_1082_ = lean_ctor_get(v_val_1081_, 4);
lean_inc(v_numFields_1082_);
lean_dec_ref(v_val_1081_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_nat_dec_eq(v_numFields_1082_, v___x_1083_);
lean_dec(v_numFields_1082_);
v___x_1085_ = lean_box(v___x_1084_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1085_);
v___x_1087_ = v___x_1075_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1085_);
v___x_1087_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
v___y_1078_ = v___x_1087_;
v_a_1079_ = v___x_1084_;
goto v___jp_1077_;
}
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1091_; 
lean_dec(v_a_1073_);
v___x_1089_ = lean_box(v___x_1060_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1089_);
v___x_1091_ = v___x_1075_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___x_1089_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
v___y_1078_ = v___x_1091_;
v_a_1079_ = v___x_1060_;
goto v___jp_1077_;
}
}
v___jp_1077_:
{
if (v_a_1079_ == 0)
{
lean_dec(v_tail_1071_);
lean_dec_ref(v___y_1064_);
return v___y_1078_;
}
else
{
lean_dec_ref(v___y_1078_);
v_x_1061_ = v_tail_1071_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec(v_tail_1071_);
lean_dec_ref(v___y_1064_);
v_a_1094_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1072_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1072_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(lean_object* v___x_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
uint8_t v___x_29136__boxed_1109_; lean_object* v_res_1110_; 
v___x_29136__boxed_1109_ = lean_unbox(v___x_1102_);
v_res_1110_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v___x_29136__boxed_1109_, v_x_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9(lean_object* v_declName_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_, lean_object* v___y_1115_){
_start:
{
lean_object* v___x_1117_; 
lean_inc_ref(v___y_1114_);
v___x_1117_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_declName_1111_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1173_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1173_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1173_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
if (lean_obj_tag(v_a_1118_) == 5)
{
lean_object* v_val_1122_; lean_object* v_toConstantVal_1123_; lean_object* v_numParams_1124_; lean_object* v_numIndices_1125_; lean_object* v_ctors_1126_; uint8_t v_isRec_1127_; uint8_t v_isUnsafe_1128_; lean_object* v_type_1129_; uint8_t v___x_1130_; 
v_val_1122_ = lean_ctor_get(v_a_1118_, 0);
lean_inc_ref(v_val_1122_);
lean_dec_ref(v_a_1118_);
v_toConstantVal_1123_ = lean_ctor_get(v_val_1122_, 0);
v_numParams_1124_ = lean_ctor_get(v_val_1122_, 1);
lean_inc(v_numParams_1124_);
v_numIndices_1125_ = lean_ctor_get(v_val_1122_, 2);
lean_inc(v_numIndices_1125_);
v_ctors_1126_ = lean_ctor_get(v_val_1122_, 4);
lean_inc(v_ctors_1126_);
v_isRec_1127_ = lean_ctor_get_uint8(v_val_1122_, sizeof(void*)*6);
v_isUnsafe_1128_ = lean_ctor_get_uint8(v_val_1122_, sizeof(void*)*6 + 1);
v_type_1129_ = lean_ctor_get(v_toConstantVal_1123_, 2);
v___x_1130_ = l_Lean_Expr_isProp(v_type_1129_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1131_ = l_Lean_InductiveVal_numTypeFormers(v_val_1122_);
lean_dec_ref(v_val_1122_);
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_dec_eq(v___x_1131_, v___x_1132_);
lean_dec(v___x_1131_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
lean_dec(v_ctors_1126_);
lean_dec(v_numIndices_1125_);
lean_dec(v_numParams_1124_);
lean_dec_ref(v___y_1114_);
v___x_1134_ = lean_box(v___x_1133_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1134_);
v___x_1136_ = v___x_1120_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
else
{
lean_object* v___x_1138_; uint8_t v___x_1139_; 
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_nat_dec_eq(v_numIndices_1125_, v___x_1138_);
lean_dec(v_numIndices_1125_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
lean_dec(v_ctors_1126_);
lean_dec(v_numParams_1124_);
lean_dec_ref(v___y_1114_);
v___x_1140_ = lean_box(v___x_1139_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1140_);
v___x_1142_ = v___x_1120_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_nat_dec_eq(v_numParams_1124_, v___x_1138_);
lean_dec(v_numParams_1124_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_ctors_1126_);
lean_dec_ref(v___y_1114_);
v___x_1145_ = lean_box(v___x_1144_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1145_);
v___x_1147_ = v___x_1120_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
uint8_t v___x_1149_; 
v___x_1149_ = l_List_isEmpty___redArg(v_ctors_1126_);
if (v___x_1149_ == 0)
{
if (v_isRec_1127_ == 0)
{
if (v_isUnsafe_1128_ == 0)
{
lean_object* v___x_1150_; 
lean_del_object(v___x_1120_);
v___x_1150_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v_isUnsafe_1128_, v_ctors_1126_, v___y_1112_, v___y_1113_, v___y_1114_, v___y_1115_);
return v___x_1150_;
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
lean_dec(v_ctors_1126_);
lean_dec_ref(v___y_1114_);
v___x_1151_ = lean_box(v_isRec_1127_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1151_);
v___x_1153_ = v___x_1120_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
else
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_dec(v_ctors_1126_);
lean_dec_ref(v___y_1114_);
v___x_1155_ = lean_box(v___x_1149_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1155_);
v___x_1157_ = v___x_1120_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_dec(v_ctors_1126_);
lean_dec_ref(v___y_1114_);
v___x_1159_ = lean_box(v___x_1130_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1159_);
v___x_1161_ = v___x_1120_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
else
{
uint8_t v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_dec(v_ctors_1126_);
lean_dec(v_numIndices_1125_);
lean_dec(v_numParams_1124_);
lean_dec_ref(v_val_1122_);
lean_dec_ref(v___y_1114_);
v___x_1163_ = 0;
v___x_1164_ = lean_box(v___x_1163_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1164_);
v___x_1166_ = v___x_1120_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
lean_dec(v_a_1118_);
lean_dec_ref(v___y_1114_);
v___x_1168_ = 0;
v___x_1169_ = lean_box(v___x_1168_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1169_);
v___x_1171_ = v___x_1120_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v___x_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v___y_1114_);
v_a_1174_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1176_ = v___x_1117_;
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_a_1174_);
lean_dec(v___x_1117_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1181_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1179_; 
if (v_isShared_1177_ == 0)
{
v___x_1179_ = v___x_1176_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(lean_object* v_declName_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_declName_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
lean_dec(v___y_1186_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1189_, lean_object* v_b_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = lean_apply_6(v_k_1189_, v_b_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, lean_box(0));
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1197_, lean_object* v_b_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1197_, v_b_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1205_, uint8_t v_bi_1206_, lean_object* v_type_1207_, lean_object* v_k_1208_, uint8_t v_kind_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_){
_start:
{
lean_object* v___f_1215_; lean_object* v___x_1216_; 
v___f_1215_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1215_, 0, v_k_1208_);
v___x_1216_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1205_, v_bi_1206_, v_type_1207_, v___f_1215_, v_kind_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
v_a_1217_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1216_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1216_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
v_a_1225_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1216_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1216_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1233_, lean_object* v_bi_1234_, lean_object* v_type_1235_, lean_object* v_k_1236_, lean_object* v_kind_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_bi_boxed_1243_; uint8_t v_kind_boxed_1244_; lean_object* v_res_1245_; 
v_bi_boxed_1243_ = lean_unbox(v_bi_1234_);
v_kind_boxed_1244_ = lean_unbox(v_kind_1237_);
v_res_1245_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1233_, v_bi_boxed_1243_, v_type_1235_, v_k_1236_, v_kind_boxed_1244_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(lean_object* v_name_1246_, lean_object* v_type_1247_, lean_object* v_k_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_){
_start:
{
uint8_t v___x_1254_; uint8_t v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = 0;
v___x_1255_ = 0;
v___x_1256_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1246_, v___x_1254_, v_type_1247_, v_k_1248_, v___x_1255_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1257_, lean_object* v_type_1258_, lean_object* v_k_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_1257_, v_type_1258_, v_k_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(lean_object* v_env_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; lean_object* v_nextMacroScope_1271_; lean_object* v_ngen_1272_; lean_object* v_auxDeclNGen_1273_; lean_object* v_traceState_1274_; lean_object* v_messages_1275_; lean_object* v_infoState_1276_; lean_object* v_snapshotTasks_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1303_; 
v___x_1270_ = lean_st_ref_take(v___y_1268_);
v_nextMacroScope_1271_ = lean_ctor_get(v___x_1270_, 1);
v_ngen_1272_ = lean_ctor_get(v___x_1270_, 2);
v_auxDeclNGen_1273_ = lean_ctor_get(v___x_1270_, 3);
v_traceState_1274_ = lean_ctor_get(v___x_1270_, 4);
v_messages_1275_ = lean_ctor_get(v___x_1270_, 6);
v_infoState_1276_ = lean_ctor_get(v___x_1270_, 7);
v_snapshotTasks_1277_ = lean_ctor_get(v___x_1270_, 8);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1303_ == 0)
{
lean_object* v_unused_1304_; lean_object* v_unused_1305_; 
v_unused_1304_ = lean_ctor_get(v___x_1270_, 5);
lean_dec(v_unused_1304_);
v_unused_1305_ = lean_ctor_get(v___x_1270_, 0);
lean_dec(v_unused_1305_);
v___x_1279_ = v___x_1270_;
v_isShared_1280_ = v_isSharedCheck_1303_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_snapshotTasks_1277_);
lean_inc(v_infoState_1276_);
lean_inc(v_messages_1275_);
lean_inc(v_traceState_1274_);
lean_inc(v_auxDeclNGen_1273_);
lean_inc(v_ngen_1272_);
lean_inc(v_nextMacroScope_1271_);
lean_dec(v___x_1270_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1303_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1281_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 5, v___x_1281_);
lean_ctor_set(v___x_1279_, 0, v_env_1266_);
v___x_1283_ = v___x_1279_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_env_1266_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_nextMacroScope_1271_);
lean_ctor_set(v_reuseFailAlloc_1302_, 2, v_ngen_1272_);
lean_ctor_set(v_reuseFailAlloc_1302_, 3, v_auxDeclNGen_1273_);
lean_ctor_set(v_reuseFailAlloc_1302_, 4, v_traceState_1274_);
lean_ctor_set(v_reuseFailAlloc_1302_, 5, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1302_, 6, v_messages_1275_);
lean_ctor_set(v_reuseFailAlloc_1302_, 7, v_infoState_1276_);
lean_ctor_set(v_reuseFailAlloc_1302_, 8, v_snapshotTasks_1277_);
v___x_1283_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v_mctx_1286_; lean_object* v_zetaDeltaFVarIds_1287_; lean_object* v_postponed_1288_; lean_object* v_diag_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1300_; 
v___x_1284_ = lean_st_ref_set(v___y_1268_, v___x_1283_);
v___x_1285_ = lean_st_ref_take(v___y_1267_);
v_mctx_1286_ = lean_ctor_get(v___x_1285_, 0);
v_zetaDeltaFVarIds_1287_ = lean_ctor_get(v___x_1285_, 2);
v_postponed_1288_ = lean_ctor_get(v___x_1285_, 3);
v_diag_1289_ = lean_ctor_get(v___x_1285_, 4);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1300_ == 0)
{
lean_object* v_unused_1301_; 
v_unused_1301_ = lean_ctor_get(v___x_1285_, 1);
lean_dec(v_unused_1301_);
v___x_1291_ = v___x_1285_;
v_isShared_1292_ = v_isSharedCheck_1300_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_diag_1289_);
lean_inc(v_postponed_1288_);
lean_inc(v_zetaDeltaFVarIds_1287_);
lean_inc(v_mctx_1286_);
lean_dec(v___x_1285_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1300_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; lean_object* v___x_1295_; 
v___x_1293_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 1, v___x_1293_);
v___x_1295_ = v___x_1291_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_mctx_1286_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1299_, 2, v_zetaDeltaFVarIds_1287_);
lean_ctor_set(v_reuseFailAlloc_1299_, 3, v_postponed_1288_);
lean_ctor_set(v_reuseFailAlloc_1299_, 4, v_diag_1289_);
v___x_1295_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = lean_st_ref_set(v___y_1267_, v___x_1295_);
v___x_1297_ = lean_box(0);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object* v_env_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_1306_, v___y_1307_, v___y_1308_);
lean_dec(v___y_1308_);
lean_dec(v___y_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(lean_object* v_declName_1311_, lean_object* v_entry_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v_env_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_st_ref_get(v___y_1316_);
v_env_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_ref(v_env_1319_);
lean_dec(v___x_1318_);
v___x_1320_ = l_Lean_Linter_deprecatedAttr;
v___x_1321_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1320_, v_env_1319_, v_declName_1311_, v_entry_1312_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1331_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1331_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1331_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set_tag(v___x_1324_, 3);
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1328_ = l_Lean_MessageData_ofFormat(v___x_1327_);
v___x_1329_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_1328_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
return v___x_1329_;
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1333_; 
v_a_1332_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1332_);
lean_dec_ref(v___x_1321_);
v___x_1333_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_a_1332_, v___y_1314_, v___y_1316_);
return v___x_1333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(lean_object* v_declName_1334_, lean_object* v_entry_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v_declName_1334_, v_entry_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(lean_object* v_declName_1342_, uint8_t v_s_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v_env_1348_; lean_object* v_nextMacroScope_1349_; lean_object* v_ngen_1350_; lean_object* v_auxDeclNGen_1351_; lean_object* v_traceState_1352_; lean_object* v_messages_1353_; lean_object* v_infoState_1354_; lean_object* v_snapshotTasks_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1384_; 
v___x_1347_ = lean_st_ref_take(v___y_1345_);
v_env_1348_ = lean_ctor_get(v___x_1347_, 0);
v_nextMacroScope_1349_ = lean_ctor_get(v___x_1347_, 1);
v_ngen_1350_ = lean_ctor_get(v___x_1347_, 2);
v_auxDeclNGen_1351_ = lean_ctor_get(v___x_1347_, 3);
v_traceState_1352_ = lean_ctor_get(v___x_1347_, 4);
v_messages_1353_ = lean_ctor_get(v___x_1347_, 6);
v_infoState_1354_ = lean_ctor_get(v___x_1347_, 7);
v_snapshotTasks_1355_ = lean_ctor_get(v___x_1347_, 8);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1384_ == 0)
{
lean_object* v_unused_1385_; 
v_unused_1385_ = lean_ctor_get(v___x_1347_, 5);
lean_dec(v_unused_1385_);
v___x_1357_ = v___x_1347_;
v_isShared_1358_ = v_isSharedCheck_1384_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snapshotTasks_1355_);
lean_inc(v_infoState_1354_);
lean_inc(v_messages_1353_);
lean_inc(v_traceState_1352_);
lean_inc(v_auxDeclNGen_1351_);
lean_inc(v_ngen_1350_);
lean_inc(v_nextMacroScope_1349_);
lean_inc(v_env_1348_);
lean_dec(v___x_1347_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1384_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
uint8_t v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1359_ = 0;
v___x_1360_ = lean_box(0);
v___x_1361_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1348_, v_declName_1342_, v_s_1343_, v___x_1359_, v___x_1360_);
v___x_1362_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 5, v___x_1362_);
lean_ctor_set(v___x_1357_, 0, v___x_1361_);
v___x_1364_ = v___x_1357_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1361_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v_nextMacroScope_1349_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_ngen_1350_);
lean_ctor_set(v_reuseFailAlloc_1383_, 3, v_auxDeclNGen_1351_);
lean_ctor_set(v_reuseFailAlloc_1383_, 4, v_traceState_1352_);
lean_ctor_set(v_reuseFailAlloc_1383_, 5, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1383_, 6, v_messages_1353_);
lean_ctor_set(v_reuseFailAlloc_1383_, 7, v_infoState_1354_);
lean_ctor_set(v_reuseFailAlloc_1383_, 8, v_snapshotTasks_1355_);
v___x_1364_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v_mctx_1367_; lean_object* v_zetaDeltaFVarIds_1368_; lean_object* v_postponed_1369_; lean_object* v_diag_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1381_; 
v___x_1365_ = lean_st_ref_set(v___y_1345_, v___x_1364_);
v___x_1366_ = lean_st_ref_take(v___y_1344_);
v_mctx_1367_ = lean_ctor_get(v___x_1366_, 0);
v_zetaDeltaFVarIds_1368_ = lean_ctor_get(v___x_1366_, 2);
v_postponed_1369_ = lean_ctor_get(v___x_1366_, 3);
v_diag_1370_ = lean_ctor_get(v___x_1366_, 4);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1381_ == 0)
{
lean_object* v_unused_1382_; 
v_unused_1382_ = lean_ctor_get(v___x_1366_, 1);
lean_dec(v_unused_1382_);
v___x_1372_ = v___x_1366_;
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_diag_1370_);
lean_inc(v_postponed_1369_);
lean_inc(v_zetaDeltaFVarIds_1368_);
lean_inc(v_mctx_1367_);
lean_dec(v___x_1366_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_mctx_1367_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_zetaDeltaFVarIds_1368_);
lean_ctor_set(v_reuseFailAlloc_1380_, 3, v_postponed_1369_);
lean_ctor_set(v_reuseFailAlloc_1380_, 4, v_diag_1370_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; 
v___x_1377_ = lean_st_ref_set(v___y_1344_, v___x_1376_);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1378_);
return v___x_1379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object* v_declName_1386_, lean_object* v_s_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_s_boxed_1391_; lean_object* v_res_1392_; 
v_s_boxed_1391_ = lean_unbox(v_s_1387_);
v_res_1392_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1386_, v_s_boxed_1391_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(lean_object* v_declName_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = 0;
v___x_1400_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1393_, v___x_1399_, v___y_1395_, v___y_1397_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(lean_object* v_declName_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v_declName_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1(lean_object* v___x_1414_, lean_object* v___x_1415_, lean_object* v_xs_1416_, uint8_t v___x_1417_, uint8_t v___x_1418_, lean_object* v_val_1419_, lean_object* v___x_1420_, lean_object* v___x_1421_, lean_object* v___x_1422_, lean_object* v___x_1423_, lean_object* v_ctors_1424_, lean_object* v___x_1425_, lean_object* v___x_1426_, lean_object* v_levelParams_1427_, lean_object* v_indName_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v___x_1434_; 
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
lean_inc_ref(v___x_1415_);
lean_inc_ref(v___x_1414_);
v___x_1434_ = l_Lean_mkArrow(v___x_1414_, v___x_1415_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1434_) == 0)
{
lean_object* v_a_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; 
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = 1;
v___x_1437_ = l_Lean_Meta_mkForallFVars(v_xs_1416_, v_a_1435_, v___x_1417_, v___x_1418_, v___x_1418_, v___x_1436_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___f_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v_a_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc(v_a_1438_);
lean_dec_ref(v___x_1437_);
v___x_1439_ = lean_box(v___x_1417_);
v___x_1440_ = lean_box(v___x_1418_);
v___x_1441_ = lean_box(v___x_1436_);
lean_inc(v___x_1421_);
lean_inc_ref(v_val_1419_);
v___f_1442_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1442_, 0, v_xs_1416_);
lean_closure_set(v___f_1442_, 1, v___x_1439_);
lean_closure_set(v___f_1442_, 2, v___x_1440_);
lean_closure_set(v___f_1442_, 3, v___x_1441_);
lean_closure_set(v___f_1442_, 4, v_val_1419_);
lean_closure_set(v___f_1442_, 5, v___x_1420_);
lean_closure_set(v___f_1442_, 6, v___x_1415_);
lean_closure_set(v___f_1442_, 7, v___x_1421_);
lean_closure_set(v___f_1442_, 8, v___x_1422_);
lean_closure_set(v___f_1442_, 9, v___x_1423_);
lean_closure_set(v___f_1442_, 10, v_ctors_1424_);
lean_closure_set(v___f_1442_, 11, v___x_1425_);
v___x_1443_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__1));
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
lean_inc(v___y_1430_);
lean_inc_ref(v___y_1429_);
v___x_1444_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v___x_1443_, v___x_1414_, v___f_1442_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v_a_1445_; lean_object* v___x_1446_; lean_object* v_env_1447_; uint32_t v___x_1448_; uint32_t v___x_1449_; uint32_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v_a_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1654_; 
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
lean_inc(v_a_1445_);
lean_dec_ref(v___x_1444_);
v___x_1446_ = lean_st_ref_get(v___y_1432_);
v_env_1447_ = lean_ctor_get(v___x_1446_, 0);
lean_inc_ref(v_env_1447_);
lean_dec(v___x_1446_);
lean_inc(v_a_1445_);
v___x_1448_ = l_Lean_getMaxHeight(v_env_1447_, v_a_1445_);
v___x_1449_ = 1;
v___x_1450_ = lean_uint32_add(v___x_1448_, v___x_1449_);
v___x_1451_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1451_, 0, v___x_1450_);
lean_inc(v_a_1438_);
lean_inc(v_levelParams_1427_);
lean_inc(v___x_1426_);
v___x_1452_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1426_, v_levelParams_1427_, v_a_1438_, v_a_1445_, v___x_1451_, v___y_1432_);
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1654_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1654_ == 0)
{
v___x_1455_ = v___x_1452_;
v_isShared_1456_ = v_isSharedCheck_1654_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_a_1453_);
lean_dec(v___x_1452_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1654_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1458_; 
if (v_isShared_1456_ == 0)
{
lean_ctor_set_tag(v___x_1455_, 1);
v___x_1458_ = v___x_1455_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v_a_1453_);
v___x_1458_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___x_1579_; 
lean_inc(v___y_1432_);
lean_inc_ref(v___y_1431_);
lean_inc_ref(v___x_1458_);
v___x_1579_ = l_Lean_addDecl(v___x_1458_, v___x_1417_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1580_; lean_object* v_env_1581_; lean_object* v_nextMacroScope_1582_; lean_object* v_ngen_1583_; lean_object* v_auxDeclNGen_1584_; lean_object* v_traceState_1585_; lean_object* v_messages_1586_; lean_object* v_infoState_1587_; lean_object* v_snapshotTasks_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1651_; 
lean_dec_ref(v___x_1579_);
v___x_1580_ = lean_st_ref_take(v___y_1432_);
v_env_1581_ = lean_ctor_get(v___x_1580_, 0);
v_nextMacroScope_1582_ = lean_ctor_get(v___x_1580_, 1);
v_ngen_1583_ = lean_ctor_get(v___x_1580_, 2);
v_auxDeclNGen_1584_ = lean_ctor_get(v___x_1580_, 3);
v_traceState_1585_ = lean_ctor_get(v___x_1580_, 4);
v_messages_1586_ = lean_ctor_get(v___x_1580_, 6);
v_infoState_1587_ = lean_ctor_get(v___x_1580_, 7);
v_snapshotTasks_1588_ = lean_ctor_get(v___x_1580_, 8);
v_isSharedCheck_1651_ = !lean_is_exclusive(v___x_1580_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; 
v_unused_1652_ = lean_ctor_get(v___x_1580_, 5);
lean_dec(v_unused_1652_);
v___x_1590_ = v___x_1580_;
v_isShared_1591_ = v_isSharedCheck_1651_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_snapshotTasks_1588_);
lean_inc(v_infoState_1587_);
lean_inc(v_messages_1586_);
lean_inc(v_traceState_1585_);
lean_inc(v_auxDeclNGen_1584_);
lean_inc(v_ngen_1583_);
lean_inc(v_nextMacroScope_1582_);
lean_inc(v_env_1581_);
lean_dec(v___x_1580_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1651_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
lean_inc(v___x_1426_);
v___x_1592_ = l_Lean_Meta_addToCompletionBlackList(v_env_1581_, v___x_1426_);
v___x_1593_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 5, v___x_1593_);
lean_ctor_set(v___x_1590_, 0, v___x_1592_);
v___x_1595_ = v___x_1590_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_nextMacroScope_1582_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_ngen_1583_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_auxDeclNGen_1584_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_traceState_1585_);
lean_ctor_set(v_reuseFailAlloc_1650_, 5, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1650_, 6, v_messages_1586_);
lean_ctor_set(v_reuseFailAlloc_1650_, 7, v_infoState_1587_);
lean_ctor_set(v_reuseFailAlloc_1650_, 8, v_snapshotTasks_1588_);
v___x_1595_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_mctx_1598_; lean_object* v_zetaDeltaFVarIds_1599_; lean_object* v_postponed_1600_; lean_object* v_diag_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1648_; 
v___x_1596_ = lean_st_ref_set(v___y_1432_, v___x_1595_);
v___x_1597_ = lean_st_ref_take(v___y_1430_);
v_mctx_1598_ = lean_ctor_get(v___x_1597_, 0);
v_zetaDeltaFVarIds_1599_ = lean_ctor_get(v___x_1597_, 2);
v_postponed_1600_ = lean_ctor_get(v___x_1597_, 3);
v_diag_1601_ = lean_ctor_get(v___x_1597_, 4);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; 
v_unused_1649_ = lean_ctor_get(v___x_1597_, 1);
lean_dec(v_unused_1649_);
v___x_1603_ = v___x_1597_;
v_isShared_1604_ = v_isSharedCheck_1648_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_diag_1601_);
lean_inc(v_postponed_1600_);
lean_inc(v_zetaDeltaFVarIds_1599_);
lean_inc(v_mctx_1598_);
lean_dec(v___x_1597_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1648_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_mctx_1598_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_zetaDeltaFVarIds_1599_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_postponed_1600_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_diag_1601_);
v___x_1607_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v_env_1610_; lean_object* v_nextMacroScope_1611_; lean_object* v_ngen_1612_; lean_object* v_auxDeclNGen_1613_; lean_object* v_traceState_1614_; lean_object* v_messages_1615_; lean_object* v_infoState_1616_; lean_object* v_snapshotTasks_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1645_; 
v___x_1608_ = lean_st_ref_set(v___y_1430_, v___x_1607_);
v___x_1609_ = lean_st_ref_take(v___y_1432_);
v_env_1610_ = lean_ctor_get(v___x_1609_, 0);
v_nextMacroScope_1611_ = lean_ctor_get(v___x_1609_, 1);
v_ngen_1612_ = lean_ctor_get(v___x_1609_, 2);
v_auxDeclNGen_1613_ = lean_ctor_get(v___x_1609_, 3);
v_traceState_1614_ = lean_ctor_get(v___x_1609_, 4);
v_messages_1615_ = lean_ctor_get(v___x_1609_, 6);
v_infoState_1616_ = lean_ctor_get(v___x_1609_, 7);
v_snapshotTasks_1617_ = lean_ctor_get(v___x_1609_, 8);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v___x_1609_, 5);
lean_dec(v_unused_1646_);
v___x_1619_ = v___x_1609_;
v_isShared_1620_ = v_isSharedCheck_1645_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_snapshotTasks_1617_);
lean_inc(v_infoState_1616_);
lean_inc(v_messages_1615_);
lean_inc(v_traceState_1614_);
lean_inc(v_auxDeclNGen_1613_);
lean_inc(v_ngen_1612_);
lean_inc(v_nextMacroScope_1611_);
lean_inc(v_env_1610_);
lean_dec(v___x_1609_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1645_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
lean_inc(v___x_1426_);
v___x_1621_ = l_Lean_addProtected(v_env_1610_, v___x_1426_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 5, v___x_1593_);
lean_ctor_set(v___x_1619_, 0, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_nextMacroScope_1611_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_ngen_1612_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_auxDeclNGen_1613_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_traceState_1614_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v___x_1593_);
lean_ctor_set(v_reuseFailAlloc_1644_, 6, v_messages_1615_);
lean_ctor_set(v_reuseFailAlloc_1644_, 7, v_infoState_1616_);
lean_ctor_set(v_reuseFailAlloc_1644_, 8, v_snapshotTasks_1617_);
v___x_1623_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_mctx_1626_; lean_object* v_zetaDeltaFVarIds_1627_; lean_object* v_postponed_1628_; lean_object* v_diag_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1642_; 
v___x_1624_ = lean_st_ref_set(v___y_1432_, v___x_1623_);
v___x_1625_ = lean_st_ref_take(v___y_1430_);
v_mctx_1626_ = lean_ctor_get(v___x_1625_, 0);
v_zetaDeltaFVarIds_1627_ = lean_ctor_get(v___x_1625_, 2);
v_postponed_1628_ = lean_ctor_get(v___x_1625_, 3);
v_diag_1629_ = lean_ctor_get(v___x_1625_, 4);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; 
v_unused_1643_ = lean_ctor_get(v___x_1625_, 1);
lean_dec(v_unused_1643_);
v___x_1631_ = v___x_1625_;
v_isShared_1632_ = v_isSharedCheck_1642_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_diag_1629_);
lean_inc(v_postponed_1628_);
lean_inc(v_zetaDeltaFVarIds_1627_);
lean_inc(v_mctx_1626_);
lean_dec(v___x_1625_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1642_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v___x_1605_);
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_mctx_1626_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v_zetaDeltaFVarIds_1627_);
lean_ctor_set(v_reuseFailAlloc_1641_, 3, v_postponed_1628_);
lean_ctor_set(v_reuseFailAlloc_1641_, 4, v_diag_1629_);
v___x_1634_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1635_ = lean_st_ref_set(v___y_1430_, v___x_1634_);
v___x_1636_ = lean_unsigned_to_nat(1u);
v___x_1637_ = l_Lean_InductiveVal_numCtors(v_val_1419_);
lean_dec_ref(v_val_1419_);
v___x_1638_ = lean_nat_dec_eq(v___x_1637_, v___x_1636_);
lean_dec(v___x_1637_);
if (v___x_1638_ == 0)
{
v___y_1460_ = v___y_1429_;
v___y_1461_ = v___y_1430_;
v___y_1462_ = v___y_1431_;
v___y_1463_ = v___y_1432_;
goto v___jp_1459_;
}
else
{
uint8_t v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = 2;
lean_inc(v___x_1426_);
v___x_1640_ = l_Lean_Meta_setInlineAttribute(v___x_1426_, v___x_1639_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
if (lean_obj_tag(v___x_1640_) == 0)
{
lean_dec_ref(v___x_1640_);
v___y_1460_ = v___y_1429_;
v___y_1461_ = v___y_1430_;
v___y_1462_ = v___y_1431_;
v___y_1463_ = v___y_1432_;
goto v___jp_1459_;
}
else
{
lean_dec_ref(v___x_1458_);
lean_dec(v_a_1438_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1421_);
return v___x_1640_;
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
else
{
lean_dec_ref(v___x_1458_);
lean_dec(v_a_1438_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1421_);
lean_dec_ref(v_val_1419_);
return v___x_1579_;
}
v___jp_1459_:
{
lean_object* v___x_1464_; 
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
v___x_1464_ = l_Lean_compileDecl(v___x_1458_, v___x_1418_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
lean_dec_ref(v___x_1464_);
lean_inc_ref(v___y_1462_);
lean_inc(v___x_1426_);
v___x_1465_ = l_Lean_enableRealizationsForConst(v___x_1426_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1465_) == 0)
{
lean_object* v___x_1466_; 
lean_dec_ref(v___x_1465_);
lean_inc_ref(v___y_1462_);
lean_inc(v_indName_1428_);
v___x_1466_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_indName_1428_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1570_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_1570_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1570_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_unbox(v_a_1467_);
lean_dec(v_a_1467_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_a_1438_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1421_);
v___x_1472_ = lean_box(0);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1472_);
v___x_1474_ = v___x_1469_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1472_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1569_; 
lean_del_object(v___x_1469_);
v___x_1476_ = l_mkToCtorIdxName(v_indName_1428_);
lean_inc(v___x_1426_);
v___x_1477_ = l_Lean_mkConst(v___x_1426_, v___x_1421_);
v___x_1478_ = lean_box(1);
lean_inc(v___x_1476_);
v___x_1479_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1476_, v_levelParams_1427_, v_a_1438_, v___x_1477_, v___x_1478_, v___y_1463_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1569_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1569_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
lean_ctor_set_tag(v___x_1482_, 1);
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; 
lean_inc(v___y_1463_);
lean_inc_ref(v___y_1462_);
v___x_1486_ = l_Lean_addAndCompile(v___x_1485_, v___x_1418_, v___y_1462_, v___y_1463_);
if (lean_obj_tag(v___x_1486_) == 0)
{
lean_object* v___x_1487_; lean_object* v_env_1488_; lean_object* v_nextMacroScope_1489_; lean_object* v_ngen_1490_; lean_object* v_auxDeclNGen_1491_; lean_object* v_traceState_1492_; lean_object* v_messages_1493_; lean_object* v_infoState_1494_; lean_object* v_snapshotTasks_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v___x_1486_);
v___x_1487_ = lean_st_ref_take(v___y_1463_);
v_env_1488_ = lean_ctor_get(v___x_1487_, 0);
v_nextMacroScope_1489_ = lean_ctor_get(v___x_1487_, 1);
v_ngen_1490_ = lean_ctor_get(v___x_1487_, 2);
v_auxDeclNGen_1491_ = lean_ctor_get(v___x_1487_, 3);
v_traceState_1492_ = lean_ctor_get(v___x_1487_, 4);
v_messages_1493_ = lean_ctor_get(v___x_1487_, 6);
v_infoState_1494_ = lean_ctor_get(v___x_1487_, 7);
v_snapshotTasks_1495_ = lean_ctor_get(v___x_1487_, 8);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v___x_1487_, 5);
lean_dec(v_unused_1567_);
v___x_1497_ = v___x_1487_;
v_isShared_1498_ = v_isSharedCheck_1566_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_snapshotTasks_1495_);
lean_inc(v_infoState_1494_);
lean_inc(v_messages_1493_);
lean_inc(v_traceState_1492_);
lean_inc(v_auxDeclNGen_1491_);
lean_inc(v_ngen_1490_);
lean_inc(v_nextMacroScope_1489_);
lean_inc(v_env_1488_);
lean_dec(v___x_1487_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1566_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1502_; 
lean_inc(v___x_1476_);
v___x_1499_ = l_Lean_Meta_addToCompletionBlackList(v_env_1488_, v___x_1476_);
v___x_1500_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 5, v___x_1500_);
lean_ctor_set(v___x_1497_, 0, v___x_1499_);
v___x_1502_ = v___x_1497_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1565_, 1, v_nextMacroScope_1489_);
lean_ctor_set(v_reuseFailAlloc_1565_, 2, v_ngen_1490_);
lean_ctor_set(v_reuseFailAlloc_1565_, 3, v_auxDeclNGen_1491_);
lean_ctor_set(v_reuseFailAlloc_1565_, 4, v_traceState_1492_);
lean_ctor_set(v_reuseFailAlloc_1565_, 5, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1565_, 6, v_messages_1493_);
lean_ctor_set(v_reuseFailAlloc_1565_, 7, v_infoState_1494_);
lean_ctor_set(v_reuseFailAlloc_1565_, 8, v_snapshotTasks_1495_);
v___x_1502_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v_mctx_1505_; lean_object* v_zetaDeltaFVarIds_1506_; lean_object* v_postponed_1507_; lean_object* v_diag_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1563_; 
v___x_1503_ = lean_st_ref_set(v___y_1463_, v___x_1502_);
v___x_1504_ = lean_st_ref_take(v___y_1461_);
v_mctx_1505_ = lean_ctor_get(v___x_1504_, 0);
v_zetaDeltaFVarIds_1506_ = lean_ctor_get(v___x_1504_, 2);
v_postponed_1507_ = lean_ctor_get(v___x_1504_, 3);
v_diag_1508_ = lean_ctor_get(v___x_1504_, 4);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1563_ == 0)
{
lean_object* v_unused_1564_; 
v_unused_1564_ = lean_ctor_get(v___x_1504_, 1);
lean_dec(v_unused_1564_);
v___x_1510_ = v___x_1504_;
v_isShared_1511_ = v_isSharedCheck_1563_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_diag_1508_);
lean_inc(v_postponed_1507_);
lean_inc(v_zetaDeltaFVarIds_1506_);
lean_inc(v_mctx_1505_);
lean_dec(v___x_1504_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1563_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 1, v___x_1512_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_mctx_1505_);
lean_ctor_set(v_reuseFailAlloc_1562_, 1, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1562_, 2, v_zetaDeltaFVarIds_1506_);
lean_ctor_set(v_reuseFailAlloc_1562_, 3, v_postponed_1507_);
lean_ctor_set(v_reuseFailAlloc_1562_, 4, v_diag_1508_);
v___x_1514_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_env_1517_; lean_object* v_nextMacroScope_1518_; lean_object* v_ngen_1519_; lean_object* v_auxDeclNGen_1520_; lean_object* v_traceState_1521_; lean_object* v_messages_1522_; lean_object* v_infoState_1523_; lean_object* v_snapshotTasks_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1560_; 
v___x_1515_ = lean_st_ref_set(v___y_1461_, v___x_1514_);
v___x_1516_ = lean_st_ref_take(v___y_1463_);
v_env_1517_ = lean_ctor_get(v___x_1516_, 0);
v_nextMacroScope_1518_ = lean_ctor_get(v___x_1516_, 1);
v_ngen_1519_ = lean_ctor_get(v___x_1516_, 2);
v_auxDeclNGen_1520_ = lean_ctor_get(v___x_1516_, 3);
v_traceState_1521_ = lean_ctor_get(v___x_1516_, 4);
v_messages_1522_ = lean_ctor_get(v___x_1516_, 6);
v_infoState_1523_ = lean_ctor_get(v___x_1516_, 7);
v_snapshotTasks_1524_ = lean_ctor_get(v___x_1516_, 8);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; 
v_unused_1561_ = lean_ctor_get(v___x_1516_, 5);
lean_dec(v_unused_1561_);
v___x_1526_ = v___x_1516_;
v_isShared_1527_ = v_isSharedCheck_1560_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_snapshotTasks_1524_);
lean_inc(v_infoState_1523_);
lean_inc(v_messages_1522_);
lean_inc(v_traceState_1521_);
lean_inc(v_auxDeclNGen_1520_);
lean_inc(v_ngen_1519_);
lean_inc(v_nextMacroScope_1518_);
lean_inc(v_env_1517_);
lean_dec(v___x_1516_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1560_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1528_; lean_object* v___x_1530_; 
lean_inc(v___x_1476_);
v___x_1528_ = l_Lean_addProtected(v_env_1517_, v___x_1476_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 5, v___x_1500_);
lean_ctor_set(v___x_1526_, 0, v___x_1528_);
v___x_1530_ = v___x_1526_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_nextMacroScope_1518_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_ngen_1519_);
lean_ctor_set(v_reuseFailAlloc_1559_, 3, v_auxDeclNGen_1520_);
lean_ctor_set(v_reuseFailAlloc_1559_, 4, v_traceState_1521_);
lean_ctor_set(v_reuseFailAlloc_1559_, 5, v___x_1500_);
lean_ctor_set(v_reuseFailAlloc_1559_, 6, v_messages_1522_);
lean_ctor_set(v_reuseFailAlloc_1559_, 7, v_infoState_1523_);
lean_ctor_set(v_reuseFailAlloc_1559_, 8, v_snapshotTasks_1524_);
v___x_1530_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v_mctx_1533_; lean_object* v_zetaDeltaFVarIds_1534_; lean_object* v_postponed_1535_; lean_object* v_diag_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1557_; 
v___x_1531_ = lean_st_ref_set(v___y_1463_, v___x_1530_);
v___x_1532_ = lean_st_ref_take(v___y_1461_);
v_mctx_1533_ = lean_ctor_get(v___x_1532_, 0);
v_zetaDeltaFVarIds_1534_ = lean_ctor_get(v___x_1532_, 2);
v_postponed_1535_ = lean_ctor_get(v___x_1532_, 3);
v_diag_1536_ = lean_ctor_get(v___x_1532_, 4);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1532_);
if (v_isSharedCheck_1557_ == 0)
{
lean_object* v_unused_1558_; 
v_unused_1558_ = lean_ctor_get(v___x_1532_, 1);
lean_dec(v_unused_1558_);
v___x_1538_ = v___x_1532_;
v_isShared_1539_ = v_isSharedCheck_1557_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_diag_1536_);
lean_inc(v_postponed_1535_);
lean_inc(v_zetaDeltaFVarIds_1534_);
lean_inc(v_mctx_1533_);
lean_dec(v___x_1532_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1557_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1541_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 1, v___x_1512_);
v___x_1541_ = v___x_1538_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_mctx_1533_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1556_, 2, v_zetaDeltaFVarIds_1534_);
lean_ctor_set(v_reuseFailAlloc_1556_, 3, v_postponed_1535_);
lean_ctor_set(v_reuseFailAlloc_1556_, 4, v_diag_1536_);
v___x_1541_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1554_; 
v___x_1542_ = lean_st_ref_set(v___y_1461_, v___x_1541_);
lean_inc(v___x_1476_);
v___x_1543_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v___x_1476_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1554_ == 0)
{
lean_object* v_unused_1555_; 
v_unused_1555_ = lean_ctor_get(v___x_1543_, 0);
lean_dec(v_unused_1555_);
v___x_1545_ = v___x_1543_;
v_isShared_1546_ = v_isSharedCheck_1554_;
goto v_resetjp_1544_;
}
else
{
lean_dec(v___x_1543_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1554_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set_tag(v___x_1545_, 1);
lean_ctor_set(v___x_1545_, 0, v___x_1426_);
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1426_);
v___x_1548_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1549_ = lean_box(0);
v___x_1550_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__3));
v___x_1551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1548_);
lean_ctor_set(v___x_1551_, 1, v___x_1549_);
lean_ctor_set(v___x_1551_, 2, v___x_1550_);
v___x_1552_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v___x_1476_, v___x_1551_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
return v___x_1552_;
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
else
{
lean_dec(v___x_1476_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___x_1426_);
return v___x_1486_;
}
}
}
}
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_a_1438_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1421_);
v_a_1571_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1466_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1466_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_a_1438_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1421_);
return v___x_1465_;
}
}
else
{
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_a_1438_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1421_);
return v___x_1464_;
}
}
}
}
}
else
{
lean_object* v_a_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1662_; 
lean_dec(v_a_1438_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1421_);
lean_dec_ref(v_val_1419_);
v_a_1655_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1657_ = v___x_1444_;
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_a_1655_);
lean_dec(v___x_1444_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1662_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1660_; 
if (v_isShared_1658_ == 0)
{
v___x_1660_ = v___x_1657_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1655_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1425_);
lean_dec(v_ctors_1424_);
lean_dec_ref(v___x_1423_);
lean_dec(v___x_1422_);
lean_dec(v___x_1421_);
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_val_1419_);
lean_dec_ref(v_xs_1416_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1414_);
v_a_1663_ = lean_ctor_get(v___x_1437_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1437_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1437_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1437_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v_indName_1428_);
lean_dec(v_levelParams_1427_);
lean_dec(v___x_1426_);
lean_dec(v___x_1425_);
lean_dec(v_ctors_1424_);
lean_dec_ref(v___x_1423_);
lean_dec(v___x_1422_);
lean_dec(v___x_1421_);
lean_dec_ref(v___x_1420_);
lean_dec_ref(v_val_1419_);
lean_dec_ref(v_xs_1416_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1414_);
v_a_1671_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1434_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1434_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1679_ = _args[0];
lean_object* v___x_1680_ = _args[1];
lean_object* v_xs_1681_ = _args[2];
lean_object* v___x_1682_ = _args[3];
lean_object* v___x_1683_ = _args[4];
lean_object* v_val_1684_ = _args[5];
lean_object* v___x_1685_ = _args[6];
lean_object* v___x_1686_ = _args[7];
lean_object* v___x_1687_ = _args[8];
lean_object* v___x_1688_ = _args[9];
lean_object* v_ctors_1689_ = _args[10];
lean_object* v___x_1690_ = _args[11];
lean_object* v___x_1691_ = _args[12];
lean_object* v_levelParams_1692_ = _args[13];
lean_object* v_indName_1693_ = _args[14];
lean_object* v___y_1694_ = _args[15];
lean_object* v___y_1695_ = _args[16];
lean_object* v___y_1696_ = _args[17];
lean_object* v___y_1697_ = _args[18];
lean_object* v___y_1698_ = _args[19];
_start:
{
uint8_t v___x_29701__boxed_1699_; uint8_t v___x_29702__boxed_1700_; lean_object* v_res_1701_; 
v___x_29701__boxed_1699_ = lean_unbox(v___x_1682_);
v___x_29702__boxed_1700_ = lean_unbox(v___x_1683_);
v_res_1701_ = l_mkCtorIdx___lam__1(v___x_1679_, v___x_1680_, v_xs_1681_, v___x_29701__boxed_1699_, v___x_29702__boxed_1700_, v_val_1684_, v___x_1685_, v___x_1686_, v___x_1687_, v___x_1688_, v_ctors_1689_, v___x_1690_, v___x_1691_, v_levelParams_1692_, v_indName_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(lean_object* v_bs_1702_, lean_object* v_k_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1702_, v_k_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1717_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1717_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1712_ = v___x_1709_;
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_a_1710_);
lean_dec(v___x_1709_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1717_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_a_1710_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1725_; 
v_a_1718_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1720_ = v___x_1709_;
v_isShared_1721_ = v_isSharedCheck_1725_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1709_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object* v_bs_1726_, lean_object* v_k_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_1726_, v_k_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec_ref(v_bs_1726_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(size_t v_sz_1734_, size_t v_i_1735_, lean_object* v_bs_1736_){
_start:
{
uint8_t v___x_1737_; 
v___x_1737_ = lean_usize_dec_lt(v_i_1735_, v_sz_1734_);
if (v___x_1737_ == 0)
{
return v_bs_1736_;
}
else
{
lean_object* v_v_1738_; lean_object* v___x_1739_; lean_object* v_bs_x27_1740_; lean_object* v___x_1741_; uint8_t v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; size_t v___x_1745_; size_t v___x_1746_; lean_object* v___x_1747_; 
v_v_1738_ = lean_array_uget(v_bs_1736_, v_i_1735_);
v___x_1739_ = lean_unsigned_to_nat(0u);
v_bs_x27_1740_ = lean_array_uset(v_bs_1736_, v_i_1735_, v___x_1739_);
v___x_1741_ = l_Lean_Expr_fvarId_x21(v_v_1738_);
lean_dec(v_v_1738_);
v___x_1742_ = 1;
v___x_1743_ = lean_box(v___x_1742_);
v___x_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1741_);
lean_ctor_set(v___x_1744_, 1, v___x_1743_);
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_add(v_i_1735_, v___x_1745_);
v___x_1747_ = lean_array_uset(v_bs_x27_1740_, v_i_1735_, v___x_1744_);
v_i_1735_ = v___x_1746_;
v_bs_1736_ = v___x_1747_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(lean_object* v_sz_1749_, lean_object* v_i_1750_, lean_object* v_bs_1751_){
_start:
{
size_t v_sz_boxed_1752_; size_t v_i_boxed_1753_; lean_object* v_res_1754_; 
v_sz_boxed_1752_ = lean_unbox_usize(v_sz_1749_);
lean_dec(v_sz_1749_);
v_i_boxed_1753_ = lean_unbox_usize(v_i_1750_);
lean_dec(v_i_1750_);
v_res_1754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_boxed_1752_, v_i_boxed_1753_, v_bs_1751_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(lean_object* v_bs_1755_, lean_object* v_k_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_){
_start:
{
size_t v_sz_1762_; size_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v_sz_1762_ = lean_array_size(v_bs_1755_);
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_1762_, v___x_1763_, v_bs_1755_);
v___x_1765_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v___x_1764_, v_k_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec_ref(v___x_1764_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(lean_object* v_bs_1766_, lean_object* v_k_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_1766_, v_k_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2(lean_object* v_numParams_1777_, lean_object* v_indName_1778_, lean_object* v___x_1779_, lean_object* v___x_1780_, uint8_t v___x_1781_, uint8_t v___x_1782_, lean_object* v_val_1783_, lean_object* v___x_1784_, lean_object* v_ctors_1785_, lean_object* v___x_1786_, lean_object* v_levelParams_1787_, lean_object* v_xs_1788_, lean_object* v_x_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_){
_start:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___f_1807_; lean_object* v___x_1808_; 
v___x_1795_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1777_);
lean_inc_ref(v_xs_1788_);
v___x_1796_ = l_Array_toSubarray___redArg(v_xs_1788_, v___x_1795_, v_numParams_1777_);
v___x_1797_ = l_Subarray_copy___redArg(v___x_1796_);
v___x_1798_ = lean_array_get_size(v_xs_1788_);
lean_inc_ref(v_xs_1788_);
v___x_1799_ = l_Array_toSubarray___redArg(v_xs_1788_, v_numParams_1777_, v___x_1798_);
v___x_1800_ = l_Subarray_copy___redArg(v___x_1799_);
lean_inc(v___x_1779_);
lean_inc(v_indName_1778_);
v___x_1801_ = l_Lean_mkConst(v_indName_1778_, v___x_1779_);
v___x_1802_ = l_Lean_mkAppN(v___x_1801_, v_xs_1788_);
v___x_1803_ = ((lean_object*)(l_mkCtorIdx___lam__2___closed__1));
v___x_1804_ = l_Lean_mkConst(v___x_1803_, v___x_1780_);
v___x_1805_ = lean_box(v___x_1781_);
v___x_1806_ = lean_box(v___x_1782_);
lean_inc_ref(v_xs_1788_);
v___f_1807_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1807_, 0, v___x_1802_);
lean_closure_set(v___f_1807_, 1, v___x_1804_);
lean_closure_set(v___f_1807_, 2, v_xs_1788_);
lean_closure_set(v___f_1807_, 3, v___x_1805_);
lean_closure_set(v___f_1807_, 4, v___x_1806_);
lean_closure_set(v___f_1807_, 5, v_val_1783_);
lean_closure_set(v___f_1807_, 6, v___x_1800_);
lean_closure_set(v___f_1807_, 7, v___x_1779_);
lean_closure_set(v___f_1807_, 8, v___x_1784_);
lean_closure_set(v___f_1807_, 9, v___x_1797_);
lean_closure_set(v___f_1807_, 10, v_ctors_1785_);
lean_closure_set(v___f_1807_, 11, v___x_1795_);
lean_closure_set(v___f_1807_, 12, v___x_1786_);
lean_closure_set(v___f_1807_, 13, v_levelParams_1787_);
lean_closure_set(v___f_1807_, 14, v_indName_1778_);
v___x_1808_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_xs_1788_, v___f_1807_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1809_ = _args[0];
lean_object* v_indName_1810_ = _args[1];
lean_object* v___x_1811_ = _args[2];
lean_object* v___x_1812_ = _args[3];
lean_object* v___x_1813_ = _args[4];
lean_object* v___x_1814_ = _args[5];
lean_object* v_val_1815_ = _args[6];
lean_object* v___x_1816_ = _args[7];
lean_object* v_ctors_1817_ = _args[8];
lean_object* v___x_1818_ = _args[9];
lean_object* v_levelParams_1819_ = _args[10];
lean_object* v_xs_1820_ = _args[11];
lean_object* v_x_1821_ = _args[12];
lean_object* v___y_1822_ = _args[13];
lean_object* v___y_1823_ = _args[14];
lean_object* v___y_1824_ = _args[15];
lean_object* v___y_1825_ = _args[16];
lean_object* v___y_1826_ = _args[17];
_start:
{
uint8_t v___x_30257__boxed_1827_; uint8_t v___x_30258__boxed_1828_; lean_object* v_res_1829_; 
v___x_30257__boxed_1827_ = lean_unbox(v___x_1813_);
v___x_30258__boxed_1828_ = lean_unbox(v___x_1814_);
v_res_1829_ = l_mkCtorIdx___lam__2(v_numParams_1809_, v_indName_1810_, v___x_1811_, v___x_1812_, v___x_30257__boxed_1827_, v___x_30258__boxed_1828_, v_val_1815_, v___x_1816_, v_ctors_1817_, v___x_1818_, v_levelParams_1819_, v_xs_1820_, v_x_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
lean_dec_ref(v_x_1821_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00mkCtorIdx_spec__3(lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
if (lean_obj_tag(v_a_1830_) == 0)
{
lean_object* v___x_1832_; 
v___x_1832_ = l_List_reverse___redArg(v_a_1831_);
return v___x_1832_;
}
else
{
lean_object* v_head_1833_; lean_object* v_tail_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1843_; 
v_head_1833_ = lean_ctor_get(v_a_1830_, 0);
v_tail_1834_ = lean_ctor_get(v_a_1830_, 1);
v_isSharedCheck_1843_ = !lean_is_exclusive(v_a_1830_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1836_ = v_a_1830_;
v_isShared_1837_ = v_isSharedCheck_1843_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_tail_1834_);
lean_inc(v_head_1833_);
lean_dec(v_a_1830_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1843_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1838_; lean_object* v___x_1840_; 
v___x_1838_ = l_Lean_mkLevelParam(v_head_1833_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 1, v_a_1831_);
lean_ctor_set(v___x_1836_, 0, v___x_1838_);
v___x_1840_ = v___x_1836_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v___x_1838_);
lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_a_1831_);
v___x_1840_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
v_a_1830_ = v_tail_1834_;
v_a_1831_ = v___x_1840_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1846_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_1847_ = lean_unsigned_to_nat(62u);
v___x_1848_ = lean_unsigned_to_nat(48u);
v___x_1849_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__1));
v___x_1850_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__0));
v___x_1851_ = l_mkPanicMessageWithDecl(v___x_1850_, v___x_1849_, v___x_1848_, v___x_1847_, v___x_1846_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3(lean_object* v_indName_1852_, uint8_t v___x_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_options_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v_options_1859_ = lean_ctor_get(v___y_1856_, 2);
v___x_1860_ = l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
v___x_1861_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_options_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_indName_1852_);
v___x_1862_ = lean_box(0);
v___x_1863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1950_; 
lean_inc(v_indName_1852_);
v___x_1864_ = l_mkCtorIdxName(v_indName_1852_);
lean_inc(v___x_1864_);
v___x_1865_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v___x_1864_, v___x_1861_, v___y_1857_);
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1950_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1950_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
uint8_t v___x_1870_; 
v___x_1870_ = lean_unbox(v_a_1866_);
lean_dec(v_a_1866_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1871_; 
lean_del_object(v___x_1868_);
lean_inc_ref(v___y_1856_);
lean_inc(v_indName_1852_);
v___x_1871_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_indName_1852_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___x_1871_);
if (lean_obj_tag(v_a_1872_) == 5)
{
lean_object* v_val_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1935_; 
v_val_1873_ = lean_ctor_get(v_a_1872_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_a_1872_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1875_ = v_a_1872_;
v_isShared_1876_ = v_isSharedCheck_1935_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_val_1873_);
lean_dec(v_a_1872_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1935_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v_toConstantVal_1877_; lean_object* v_numParams_1878_; lean_object* v_numIndices_1879_; lean_object* v_ctors_1880_; lean_object* v_levelParams_1881_; lean_object* v_type_1882_; lean_object* v___x_1883_; 
v_toConstantVal_1877_ = lean_ctor_get(v_val_1873_, 0);
v_numParams_1878_ = lean_ctor_get(v_val_1873_, 1);
lean_inc(v_numParams_1878_);
v_numIndices_1879_ = lean_ctor_get(v_val_1873_, 2);
lean_inc(v_numIndices_1879_);
v_ctors_1880_ = lean_ctor_get(v_val_1873_, 4);
lean_inc(v_ctors_1880_);
v_levelParams_1881_ = lean_ctor_get(v_toConstantVal_1877_, 1);
lean_inc(v_levelParams_1881_);
v_type_1882_ = lean_ctor_get(v_toConstantVal_1877_, 2);
lean_inc_ref(v_type_1882_);
lean_inc(v___y_1857_);
lean_inc_ref(v___y_1856_);
lean_inc(v___y_1855_);
lean_inc_ref(v___y_1854_);
lean_inc_ref(v_type_1882_);
v___x_1883_ = l_Lean_Meta_isPropFormerType(v_type_1882_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1926_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1886_ = v___x_1883_;
v_isShared_1887_ = v_isSharedCheck_1926_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1883_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1926_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
uint8_t v___x_1888_; 
v___x_1888_ = lean_unbox(v_a_1884_);
lean_dec(v_a_1884_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_del_object(v___x_1886_);
lean_inc(v_indName_1852_);
v___x_1889_ = l_Lean_mkCasesOnName(v_indName_1852_);
lean_inc_ref(v___y_1856_);
lean_inc(v___x_1889_);
v___x_1890_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v___x_1889_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1913_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1893_ = v___x_1890_;
v_isShared_1894_ = v_isSharedCheck_1913_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1890_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1913_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1895_ = l_List_lengthTR___redArg(v_levelParams_1881_);
v___x_1896_ = l_Lean_ConstantInfo_levelParams(v_a_1891_);
lean_dec(v_a_1891_);
v___x_1897_ = l_List_lengthTR___redArg(v___x_1896_);
lean_dec(v___x_1896_);
v___x_1898_ = lean_nat_dec_lt(v___x_1895_, v___x_1897_);
lean_dec(v___x_1897_);
lean_dec(v___x_1895_);
if (v___x_1898_ == 0)
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
lean_dec(v___x_1889_);
lean_dec_ref(v_type_1882_);
lean_dec(v_levelParams_1881_);
lean_dec(v_ctors_1880_);
lean_dec(v_numIndices_1879_);
lean_dec(v_numParams_1878_);
lean_del_object(v___x_1875_);
lean_dec_ref(v_val_1873_);
lean_dec(v___x_1864_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_indName_1852_);
v___x_1899_ = lean_box(0);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 0, v___x_1899_);
v___x_1901_ = v___x_1893_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
else
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___f_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
lean_del_object(v___x_1893_);
v___x_1903_ = lean_box(0);
lean_inc(v_levelParams_1881_);
v___x_1904_ = l_List_mapTR_loop___at___00mkCtorIdx_spec__3(v_levelParams_1881_, v___x_1903_);
v___x_1905_ = lean_box(v___x_1853_);
v___x_1906_ = lean_box(v___x_1861_);
lean_inc(v_numParams_1878_);
v___f_1907_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_1907_, 0, v_numParams_1878_);
lean_closure_set(v___f_1907_, 1, v_indName_1852_);
lean_closure_set(v___f_1907_, 2, v___x_1904_);
lean_closure_set(v___f_1907_, 3, v___x_1903_);
lean_closure_set(v___f_1907_, 4, v___x_1905_);
lean_closure_set(v___f_1907_, 5, v___x_1906_);
lean_closure_set(v___f_1907_, 6, v_val_1873_);
lean_closure_set(v___f_1907_, 7, v___x_1889_);
lean_closure_set(v___f_1907_, 8, v_ctors_1880_);
lean_closure_set(v___f_1907_, 9, v___x_1864_);
lean_closure_set(v___f_1907_, 10, v_levelParams_1881_);
v___x_1908_ = lean_nat_add(v_numParams_1878_, v_numIndices_1879_);
lean_dec(v_numIndices_1879_);
lean_dec(v_numParams_1878_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 1);
lean_ctor_set(v___x_1875_, 0, v___x_1908_);
v___x_1910_ = v___x_1875_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_1882_, v___x_1910_, v___f_1907_, v___x_1853_, v___x_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1911_;
}
}
}
}
else
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec(v___x_1889_);
lean_dec_ref(v_type_1882_);
lean_dec(v_levelParams_1881_);
lean_dec(v_ctors_1880_);
lean_dec(v_numIndices_1879_);
lean_dec(v_numParams_1878_);
lean_del_object(v___x_1875_);
lean_dec_ref(v_val_1873_);
lean_dec(v___x_1864_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_indName_1852_);
v_a_1914_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1890_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1890_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v___x_1922_; lean_object* v___x_1924_; 
lean_dec_ref(v_type_1882_);
lean_dec(v_levelParams_1881_);
lean_dec(v_ctors_1880_);
lean_dec(v_numIndices_1879_);
lean_dec(v_numParams_1878_);
lean_del_object(v___x_1875_);
lean_dec_ref(v_val_1873_);
lean_dec(v___x_1864_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_indName_1852_);
v___x_1922_ = lean_box(0);
if (v_isShared_1887_ == 0)
{
lean_ctor_set(v___x_1886_, 0, v___x_1922_);
v___x_1924_ = v___x_1886_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_dec_ref(v_type_1882_);
lean_dec(v_levelParams_1881_);
lean_dec(v_ctors_1880_);
lean_dec(v_numIndices_1879_);
lean_dec(v_numParams_1878_);
lean_del_object(v___x_1875_);
lean_dec_ref(v_val_1873_);
lean_dec(v___x_1864_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_indName_1852_);
v_a_1927_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1883_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1883_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v_a_1872_);
lean_dec(v___x_1864_);
lean_dec(v_indName_1852_);
v___x_1936_ = lean_obj_once(&l_mkCtorIdx___lam__3___closed__2, &l_mkCtorIdx___lam__3___closed__2_once, _init_l_mkCtorIdx___lam__3___closed__2);
v___x_1937_ = l_panic___at___00mkCtorIdx_spec__13(v___x_1936_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
return v___x_1937_;
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v___x_1864_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_indName_1852_);
v_a_1938_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1871_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1871_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_dec(v___x_1864_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
lean_dec_ref(v___y_1854_);
lean_dec(v_indName_1852_);
v___x_1946_ = lean_box(0);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 0, v___x_1946_);
v___x_1948_ = v___x_1868_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3___boxed(lean_object* v_indName_1951_, lean_object* v___x_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
uint8_t v___x_30370__boxed_1958_; lean_object* v_res_1959_; 
v___x_30370__boxed_1958_ = lean_unbox(v___x_1952_);
v_res_1959_ = l_mkCtorIdx___lam__3(v_indName_1951_, v___x_30370__boxed_1958_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__4(lean_object* v___x_1960_, lean_object* v_e_1961_){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = l_Lean_indentD(v_e_1961_);
v___x_1963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1960_);
lean_ctor_set(v___x_1963_, 1, v___x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5(lean_object* v___f_1964_, lean_object* v___f_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_Meta_mapErrorImp___redArg(v___f_1964_, v___f_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1979_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1979_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1977_; 
if (v_isShared_1975_ == 0)
{
v___x_1977_ = v___x_1974_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_a_1972_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1971_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1971_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5___boxed(lean_object* v___f_1988_, lean_object* v___f_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_, lean_object* v___y_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_mkCtorIdx___lam__5(v___f_1988_, v___f_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_);
return v_res_1995_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = ((lean_object*)(l_mkCtorIdx___closed__0));
v___x_1998_ = l_Lean_stringToMessageData(v___x_1997_);
return v___x_1998_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_mkCtorIdx___closed__2));
v___x_2001_ = l_Lean_stringToMessageData(v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx(lean_object* v_indName_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_){
_start:
{
lean_object* v___x_2008_; uint8_t v___x_2009_; lean_object* v___x_2010_; lean_object* v___f_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___f_2016_; lean_object* v___f_2017_; uint8_t v___x_2018_; 
v___x_2008_ = lean_obj_once(&l_mkCtorIdx___closed__1, &l_mkCtorIdx___closed__1_once, _init_l_mkCtorIdx___closed__1);
v___x_2009_ = 0;
v___x_2010_ = lean_box(v___x_2009_);
lean_inc(v_indName_2002_);
v___f_2011_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2011_, 0, v_indName_2002_);
lean_closure_set(v___f_2011_, 1, v___x_2010_);
lean_inc(v_indName_2002_);
v___x_2012_ = l_Lean_MessageData_ofConstName(v_indName_2002_, v___x_2009_);
v___x_2013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2008_);
lean_ctor_set(v___x_2013_, 1, v___x_2012_);
v___x_2014_ = lean_obj_once(&l_mkCtorIdx___closed__3, &l_mkCtorIdx___closed__3_once, _init_l_mkCtorIdx___closed__3);
v___x_2015_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
v___f_2016_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2016_, 0, v___x_2015_);
v___f_2017_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2017_, 0, v___f_2011_);
lean_closure_set(v___f_2017_, 1, v___f_2016_);
v___x_2018_ = l_Lean_isPrivateName(v_indName_2002_);
lean_dec(v_indName_2002_);
if (v___x_2018_ == 0)
{
uint8_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = 1;
v___x_2020_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2017_, v___x_2019_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
return v___x_2020_;
}
else
{
lean_object* v___x_2021_; 
v___x_2021_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2017_, v___x_2009_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_2006_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___boxed(lean_object* v_indName_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_mkCtorIdx(v_indName_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(uint8_t v___x_2029_, lean_object* v___x_2030_, lean_object* v_as_2031_, lean_object* v_as_x27_2032_, lean_object* v_b_2033_, lean_object* v_a_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v___x_2040_; 
v___x_2040_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_2029_, v___x_2030_, v_as_x27_2032_, v_b_2033_, v___y_2035_, v___y_2036_, v___y_2037_, v___y_2038_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(lean_object* v___x_2041_, lean_object* v___x_2042_, lean_object* v_as_2043_, lean_object* v_as_x27_2044_, lean_object* v_b_2045_, lean_object* v_a_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
uint8_t v___x_30689__boxed_2052_; lean_object* v_res_2053_; 
v___x_30689__boxed_2052_ = lean_unbox(v___x_2041_);
v_res_2053_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(v___x_30689__boxed_2052_, v___x_2042_, v_as_2043_, v_as_x27_2044_, v_b_2045_, v_a_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
lean_dec(v_as_2043_);
lean_dec_ref(v___x_2042_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2054_, lean_object* v_name_2055_, uint8_t v_bi_2056_, lean_object* v_type_2057_, lean_object* v_k_2058_, uint8_t v_kind_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_2055_, v_bi_2056_, v_type_2057_, v_k_2058_, v_kind_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2066_, lean_object* v_name_2067_, lean_object* v_bi_2068_, lean_object* v_type_2069_, lean_object* v_k_2070_, lean_object* v_kind_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_){
_start:
{
uint8_t v_bi_boxed_2077_; uint8_t v_kind_boxed_2078_; lean_object* v_res_2079_; 
v_bi_boxed_2077_ = lean_unbox(v_bi_2068_);
v_kind_boxed_2078_ = lean_unbox(v_kind_2071_);
v_res_2079_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(v_00_u03b1_2066_, v_name_2067_, v_bi_boxed_2077_, v_type_2069_, v_k_2070_, v_kind_boxed_2078_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(lean_object* v_00_u03b1_2080_, lean_object* v_name_2081_, lean_object* v_type_2082_, lean_object* v_k_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_2081_, v_type_2082_, v_k_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2090_, lean_object* v_name_2091_, lean_object* v_type_2092_, lean_object* v_k_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(v_00_u03b1_2090_, v_name_2091_, v_type_2092_, v_k_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(lean_object* v_declName_2100_, uint8_t v_s_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_2100_, v_s_2101_, v___y_2103_, v___y_2105_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_declName_2108_, lean_object* v_s_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
uint8_t v_s_boxed_2115_; lean_object* v_res_2116_; 
v_s_boxed_2115_ = lean_unbox(v_s_2109_);
v_res_2116_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(v_declName_2108_, v_s_boxed_2115_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
lean_dec(v___y_2113_);
lean_dec_ref(v___y_2112_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(lean_object* v_env_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_2117_, v___y_2119_, v___y_2121_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(lean_object* v_env_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(v_env_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(lean_object* v_00_u03b1_2131_, lean_object* v_bs_2132_, lean_object* v_k_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_2132_, v_k_2133_, v___y_2134_, v___y_2135_, v___y_2136_, v___y_2137_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(lean_object* v_00_u03b1_2140_, lean_object* v_bs_2141_, lean_object* v_k_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(v_00_u03b1_2140_, v_bs_2141_, v_k_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec_ref(v_bs_2141_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(lean_object* v_00_u03b1_2149_, lean_object* v_bs_2150_, lean_object* v_k_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_2150_, v_k_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_2158_, lean_object* v_bs_2159_, lean_object* v_k_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(v_00_u03b1_2158_, v_bs_2159_, v_k_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2167_, lean_object* v_constName_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_constName_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(v_00_u03b1_2175_, v_constName_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
lean_dec(v___y_2180_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2183_, lean_object* v_msg_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v___x_2190_; 
v___x_2190_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_2184_, v___y_2185_, v___y_2186_, v___y_2187_, v___y_2188_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2191_, lean_object* v_msg_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(v_00_u03b1_2191_, v_msg_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2199_, lean_object* v_ref_2200_, lean_object* v_constName_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2200_, v_constName_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2208_, lean_object* v_ref_2209_, lean_object* v_constName_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2208_, v_ref_2209_, v_constName_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v_ref_2209_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object* v_00_u03b1_2217_, lean_object* v_ref_2218_, lean_object* v_msg_2219_, lean_object* v_declHint_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; 
v___x_2226_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_2218_, v_msg_2219_, v_declHint_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object* v_00_u03b1_2227_, lean_object* v_ref_2228_, lean_object* v_msg_2229_, lean_object* v_declHint_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_2227_, v_ref_2228_, v_msg_2229_, v_declHint_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec(v___y_2232_);
lean_dec_ref(v___y_2231_);
lean_dec(v_ref_2228_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object* v_msg_2237_, lean_object* v_declHint_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_2237_, v_declHint_2238_, v___y_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object* v_msg_2245_, lean_object* v_declHint_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_2245_, v_declHint_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object* v_00_u03b1_2253_, lean_object* v_ref_2254_, lean_object* v_msg_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_2254_, v_msg_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2262_, lean_object* v_ref_2263_, lean_object* v_msg_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_2262_, v_ref_2263_, v_msg_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
lean_dec(v___y_2268_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v_ref_2263_);
return v_res_2270_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_CompletionName(uint8_t builtin);
lean_object* initialize_Lean_Linter_Deprecated(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CompletionName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Deprecated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CtorIdx(builtin);
}
#ifdef __cplusplus
}
#endif
