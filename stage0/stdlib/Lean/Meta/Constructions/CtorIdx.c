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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
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
static const lean_string_object l_mkCtorIdx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-08-25"};
static const lean_object* l_mkCtorIdx___lam__1___closed__0 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__0_value;
static const lean_ctor_object l_mkCtorIdx___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_mkCtorIdx___lam__1___closed__0_value)}};
static const lean_object* l_mkCtorIdx___lam__1___closed__1 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__1_value;
static const lean_string_object l_mkCtorIdx___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_mkCtorIdx___lam__1___closed__2 = (const lean_object*)&l_mkCtorIdx___lam__1___closed__2_value;
static const lean_ctor_object l_mkCtorIdx___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_mkCtorIdx___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
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
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
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
lean_inc(v___y_147_);
lean_inc_ref(v___y_146_);
lean_inc(v___y_145_);
lean_inc_ref(v___y_144_);
v___x_149_ = lean_apply_7(v_k_141_, v_b_142_, v_c_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_, lean_box(0));
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object* v_k_150_, lean_object* v_b_151_, lean_object* v_c_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(v_k_150_, v_b_151_, v_c_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
lean_dec(v___y_156_);
lean_dec_ref(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
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
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
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
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(lean_object* v_name_226_, lean_object* v_levelParams_227_, lean_object* v_type_228_, lean_object* v_value_229_, lean_object* v_hints_230_, lean_object* v___y_231_){
_start:
{
lean_object* v___x_233_; uint8_t v___y_235_; uint8_t v___y_242_; lean_object* v_env_245_; uint8_t v___x_246_; 
v___x_233_ = lean_st_ref_get(v___y_231_);
v_env_245_ = lean_ctor_get(v___x_233_, 0);
lean_inc_ref_n(v_env_245_, 2);
lean_dec(v___x_233_);
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
lean_object* v___f_285_; lean_object* v___x_26644__overap_286_; lean_object* v___x_287_; 
v___f_285_ = ((lean_object*)(l_panic___at___00mkCtorIdx_spec__13___closed__0));
v___x_26644__overap_286_ = lean_panic_fn_borrowed(v___f_285_, v_msg_279_);
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
lean_inc(v___y_281_);
lean_inc_ref(v___y_280_);
v___x_287_ = lean_apply_5(v___x_26644__overap_286_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, lean_box(0));
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13___boxed(lean_object* v_msg_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_panic___at___00mkCtorIdx_spec__13(v_msg_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
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
lean_inc_ref(v___y_357_);
lean_inc(v___y_356_);
lean_inc_ref(v___y_355_);
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
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec(v___y_430_);
lean_dec_ref(v___y_429_);
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
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec(v___y_449_);
lean_dec_ref(v___y_448_);
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
v___x_501_ = l_instMonadEIO(lean_box(0));
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(lean_object* v_msg_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_toApplicative_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_575_; 
v___x_512_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0);
v___x_513_ = l_StateRefT_x27_instMonad___redArg(v___x_512_);
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
v___x_537_ = l_StateRefT_x27_instMonad___redArg(v___x_536_);
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
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_30006__overap_563_; lean_object* v___x_564_; 
v___x_561_ = lean_box(0);
v___x_562_ = l_instInhabitedOfMonad___redArg(v___x_560_, v___x_561_);
v___x_30006__overap_563_ = lean_panic_fn_borrowed(v___x_562_, v_msg_506_);
lean_dec(v___x_562_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc_ref(v___y_507_);
v___x_564_ = lean_apply_5(v___x_30006__overap_563_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, lean_box(0));
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
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
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
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(lean_object* v_constName_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_constName_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
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
uint8_t v___x_34830__boxed_678_; uint8_t v___x_34831__boxed_679_; uint8_t v___x_34832__boxed_680_; lean_object* v_res_681_; 
v___x_34830__boxed_678_ = lean_unbox(v___x_668_);
v___x_34831__boxed_679_ = lean_unbox(v___x_669_);
v___x_34832__boxed_680_ = lean_unbox(v___x_670_);
v_res_681_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(v_cidx_667_, v___x_34830__boxed_678_, v___x_34831__boxed_679_, v___x_34832__boxed_680_, v_ys_671_, v_x_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
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
lean_dec_ref(v_b_685_);
return v___x_700_;
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_tail_693_);
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
uint8_t v___x_34861__boxed_736_; lean_object* v_res_737_; 
v___x_34861__boxed_736_ = lean_unbox(v___x_727_);
v_res_737_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_34861__boxed_736_, v___x_728_, v_as_x27_729_, v_b_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
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
lean_dec_ref(v_x_752_);
lean_dec_ref(v_xs_740_);
return v___x_775_;
}
}
else
{
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
uint8_t v___x_34952__boxed_796_; uint8_t v___x_34953__boxed_797_; uint8_t v___x_34954__boxed_798_; lean_object* v_res_799_; 
v___x_34952__boxed_796_ = lean_unbox(v___x_779_);
v___x_34953__boxed_797_ = lean_unbox(v___x_780_);
v___x_34954__boxed_798_ = lean_unbox(v___x_781_);
v_res_799_ = l_mkCtorIdx___lam__0(v_xs_778_, v___x_34952__boxed_796_, v___x_34953__boxed_797_, v___x_34954__boxed_798_, v_val_782_, v___x_783_, v___x_784_, v___x_785_, v___x_786_, v___x_787_, v_ctors_788_, v___x_789_, v_x_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
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
lean_object* v_fileName_941_; lean_object* v_fileMap_942_; lean_object* v_options_943_; lean_object* v_currRecDepth_944_; lean_object* v_maxRecDepth_945_; lean_object* v_ref_946_; lean_object* v_currNamespace_947_; lean_object* v_openDecls_948_; lean_object* v_initHeartbeats_949_; lean_object* v_maxHeartbeats_950_; lean_object* v_quotContext_951_; lean_object* v_currMacroScope_952_; uint8_t v_diag_953_; lean_object* v_cancelTk_x3f_954_; uint8_t v_suppressElabErrors_955_; lean_object* v_inheritedTraceOptions_956_; lean_object* v_ref_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
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
v_ref_957_ = l_Lean_replaceRef(v_ref_934_, v_ref_946_);
lean_inc_ref(v_inheritedTraceOptions_956_);
lean_inc(v_cancelTk_x3f_954_);
lean_inc(v_currMacroScope_952_);
lean_inc(v_quotContext_951_);
lean_inc(v_maxHeartbeats_950_);
lean_inc(v_initHeartbeats_949_);
lean_inc(v_openDecls_948_);
lean_inc(v_currNamespace_947_);
lean_inc(v_maxRecDepth_945_);
lean_inc(v_currRecDepth_944_);
lean_inc_ref(v_options_943_);
lean_inc_ref(v_fileMap_942_);
lean_inc_ref(v_fileName_941_);
v___x_958_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_958_, 0, v_fileName_941_);
lean_ctor_set(v___x_958_, 1, v_fileMap_942_);
lean_ctor_set(v___x_958_, 2, v_options_943_);
lean_ctor_set(v___x_958_, 3, v_currRecDepth_944_);
lean_ctor_set(v___x_958_, 4, v_maxRecDepth_945_);
lean_ctor_set(v___x_958_, 5, v_ref_957_);
lean_ctor_set(v___x_958_, 6, v_currNamespace_947_);
lean_ctor_set(v___x_958_, 7, v_openDecls_948_);
lean_ctor_set(v___x_958_, 8, v_initHeartbeats_949_);
lean_ctor_set(v___x_958_, 9, v_maxHeartbeats_950_);
lean_ctor_set(v___x_958_, 10, v_quotContext_951_);
lean_ctor_set(v___x_958_, 11, v_currMacroScope_952_);
lean_ctor_set(v___x_958_, 12, v_cancelTk_x3f_954_);
lean_ctor_set(v___x_958_, 13, v_inheritedTraceOptions_956_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*14, v_diag_953_);
lean_ctor_set_uint8(v___x_958_, sizeof(void*)*14 + 1, v_suppressElabErrors_955_);
v___x_959_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_935_, v___y_936_, v___y_937_, v___x_958_, v___y_939_);
lean_dec_ref(v___x_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object* v_ref_960_, lean_object* v_msg_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_960_, v_msg_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_);
lean_dec(v___y_965_);
lean_dec_ref(v___y_964_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v_ref_960_);
return v_res_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object* v_ref_968_, lean_object* v_msg_969_, lean_object* v_declHint_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
lean_object* v___x_976_; lean_object* v_a_977_; lean_object* v___x_978_; 
v___x_976_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_969_, v_declHint_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref(v___x_976_);
v___x_978_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_968_, v_a_977_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object* v_ref_979_, lean_object* v_msg_980_, lean_object* v_declHint_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_979_, v_msg_980_, v_declHint_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v_ref_979_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_991_, lean_object* v_constName_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_998_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_999_ = 0;
lean_inc(v_constName_992_);
v___x_1000_ = l_Lean_MessageData_ofConstName(v_constName_992_, v___x_999_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_998_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_991_, v___x_1003_, v_constName_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1005_, lean_object* v_constName_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1005_, v_constName_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v_ref_1005_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_ref_1019_; lean_object* v___x_1020_; 
v_ref_1019_ = lean_ctor_get(v___y_1016_, 5);
v___x_1020_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1019_, v_constName_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
return v_res_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(lean_object* v_constName_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; lean_object* v_env_1035_; uint8_t v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = lean_st_ref_get(v___y_1032_);
v_env_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc_ref(v_env_1035_);
lean_dec(v___x_1034_);
v___x_1036_ = 0;
lean_inc(v_constName_1028_);
v___x_1037_ = l_Lean_Environment_find_x3f(v_env_1035_, v_constName_1028_, v___x_1036_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1038_;
}
else
{
lean_object* v_val_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
lean_dec(v_constName_1028_);
v_val_1039_ = lean_ctor_get(v___x_1037_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1037_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1041_ = v___x_1037_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_val_1039_);
lean_dec(v___x_1037_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set_tag(v___x_1041_, 0);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_val_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(lean_object* v_constName_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_constName_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(uint8_t v___x_1054_, lean_object* v_x_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
if (lean_obj_tag(v_x_1055_) == 0)
{
uint8_t v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1061_ = 1;
v___x_1062_ = lean_box(v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1062_);
return v___x_1063_;
}
else
{
lean_object* v_head_1064_; lean_object* v_tail_1065_; lean_object* v___x_1066_; 
v_head_1064_ = lean_ctor_get(v_x_1055_, 0);
lean_inc(v_head_1064_);
v_tail_1065_ = lean_ctor_get(v_x_1055_, 1);
lean_inc(v_tail_1065_);
lean_dec_ref(v_x_1055_);
v___x_1066_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_head_1064_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
if (lean_obj_tag(v___x_1066_) == 0)
{
lean_object* v_a_1067_; lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1087_; 
v_a_1067_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1069_ = v___x_1066_;
v_isShared_1070_ = v_isSharedCheck_1087_;
goto v_resetjp_1068_;
}
else
{
lean_inc(v_a_1067_);
lean_dec(v___x_1066_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1087_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___y_1072_; uint8_t v_a_1073_; 
if (lean_obj_tag(v_a_1067_) == 6)
{
lean_object* v_val_1075_; lean_object* v_numFields_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v_val_1075_ = lean_ctor_get(v_a_1067_, 0);
lean_inc_ref(v_val_1075_);
lean_dec_ref(v_a_1067_);
v_numFields_1076_ = lean_ctor_get(v_val_1075_, 4);
lean_inc(v_numFields_1076_);
lean_dec_ref(v_val_1075_);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_nat_dec_eq(v_numFields_1076_, v___x_1077_);
lean_dec(v_numFields_1076_);
v___x_1079_ = lean_box(v___x_1078_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1079_);
v___x_1081_ = v___x_1069_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
v___y_1072_ = v___x_1081_;
v_a_1073_ = v___x_1078_;
goto v___jp_1071_;
}
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_dec(v_a_1067_);
v___x_1083_ = lean_box(v___x_1054_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1083_);
v___x_1085_ = v___x_1069_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
v___y_1072_ = v___x_1085_;
v_a_1073_ = v___x_1054_;
goto v___jp_1071_;
}
}
v___jp_1071_:
{
if (v_a_1073_ == 0)
{
lean_dec(v_tail_1065_);
return v___y_1072_;
}
else
{
lean_dec_ref(v___y_1072_);
v_x_1055_ = v_tail_1065_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
lean_dec(v_tail_1065_);
v_a_1088_ = lean_ctor_get(v___x_1066_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1066_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1066_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1066_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(lean_object* v___x_1096_, lean_object* v_x_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_){
_start:
{
uint8_t v___x_35470__boxed_1103_; lean_object* v_res_1104_; 
v___x_35470__boxed_1103_ = lean_unbox(v___x_1096_);
v_res_1104_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v___x_35470__boxed_1103_, v_x_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec_ref(v___y_1098_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9(lean_object* v_declName_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_declName_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1167_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1167_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1167_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
if (lean_obj_tag(v_a_1112_) == 5)
{
lean_object* v_val_1116_; lean_object* v_toConstantVal_1117_; lean_object* v_numParams_1118_; lean_object* v_numIndices_1119_; lean_object* v_ctors_1120_; uint8_t v_isRec_1121_; uint8_t v_isUnsafe_1122_; lean_object* v_type_1123_; uint8_t v___x_1124_; 
v_val_1116_ = lean_ctor_get(v_a_1112_, 0);
lean_inc_ref(v_val_1116_);
lean_dec_ref(v_a_1112_);
v_toConstantVal_1117_ = lean_ctor_get(v_val_1116_, 0);
v_numParams_1118_ = lean_ctor_get(v_val_1116_, 1);
lean_inc(v_numParams_1118_);
v_numIndices_1119_ = lean_ctor_get(v_val_1116_, 2);
lean_inc(v_numIndices_1119_);
v_ctors_1120_ = lean_ctor_get(v_val_1116_, 4);
lean_inc(v_ctors_1120_);
v_isRec_1121_ = lean_ctor_get_uint8(v_val_1116_, sizeof(void*)*6);
v_isUnsafe_1122_ = lean_ctor_get_uint8(v_val_1116_, sizeof(void*)*6 + 1);
v_type_1123_ = lean_ctor_get(v_toConstantVal_1117_, 2);
v___x_1124_ = l_Lean_Expr_isProp(v_type_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1125_ = l_Lean_InductiveVal_numTypeFormers(v_val_1116_);
lean_dec_ref(v_val_1116_);
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_dec_eq(v___x_1125_, v___x_1126_);
lean_dec(v___x_1125_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
lean_dec(v_ctors_1120_);
lean_dec(v_numIndices_1119_);
lean_dec(v_numParams_1118_);
v___x_1128_ = lean_box(v___x_1127_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1128_);
v___x_1130_ = v___x_1114_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_object* v___x_1132_; uint8_t v___x_1133_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_nat_dec_eq(v_numIndices_1119_, v___x_1132_);
lean_dec(v_numIndices_1119_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
lean_dec(v_ctors_1120_);
lean_dec(v_numParams_1118_);
v___x_1134_ = lean_box(v___x_1133_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1134_);
v___x_1136_ = v___x_1114_;
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
uint8_t v___x_1138_; 
v___x_1138_ = lean_nat_dec_eq(v_numParams_1118_, v___x_1132_);
lean_dec(v_numParams_1118_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_dec(v_ctors_1120_);
v___x_1139_ = lean_box(v___x_1138_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1139_);
v___x_1141_ = v___x_1114_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
else
{
uint8_t v___x_1143_; 
v___x_1143_ = l_List_isEmpty___redArg(v_ctors_1120_);
if (v___x_1143_ == 0)
{
if (v_isRec_1121_ == 0)
{
if (v_isUnsafe_1122_ == 0)
{
lean_object* v___x_1144_; 
lean_del_object(v___x_1114_);
v___x_1144_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v_isUnsafe_1122_, v_ctors_1120_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
return v___x_1144_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_ctors_1120_);
v___x_1145_ = lean_box(v_isRec_1121_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1145_);
v___x_1147_ = v___x_1114_;
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
}
else
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec(v_ctors_1120_);
v___x_1149_ = lean_box(v___x_1143_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1149_);
v___x_1151_ = v___x_1114_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
else
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
lean_dec(v_ctors_1120_);
v___x_1153_ = lean_box(v___x_1124_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1153_);
v___x_1155_ = v___x_1114_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
else
{
uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
lean_dec(v_ctors_1120_);
lean_dec(v_numIndices_1119_);
lean_dec(v_numParams_1118_);
lean_dec_ref(v_val_1116_);
v___x_1157_ = 0;
v___x_1158_ = lean_box(v___x_1157_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1158_);
v___x_1160_ = v___x_1114_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
lean_dec(v_a_1112_);
v___x_1162_ = 0;
v___x_1163_ = lean_box(v___x_1162_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1163_);
v___x_1165_ = v___x_1114_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_a_1168_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1111_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1111_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(lean_object* v_declName_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_declName_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1183_, lean_object* v_b_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
lean_inc(v___y_1188_);
lean_inc_ref(v___y_1187_);
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
v___x_1190_ = lean_apply_6(v_k_1183_, v_b_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, lean_box(0));
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1191_, lean_object* v_b_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_res_1198_; 
v_res_1198_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1191_, v_b_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
return v_res_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1199_, uint8_t v_bi_1200_, lean_object* v_type_1201_, lean_object* v_k_1202_, uint8_t v_kind_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___f_1209_; lean_object* v___x_1210_; 
v___f_1209_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1209_, 0, v_k_1202_);
v___x_1210_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1199_, v_bi_1200_, v_type_1201_, v___f_1209_, v_kind_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1218_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1213_ = v___x_1210_;
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1218_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1216_; 
if (v_isShared_1214_ == 0)
{
v___x_1216_ = v___x_1213_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_a_1211_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
else
{
lean_object* v_a_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
v_a_1219_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1210_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_a_1219_);
lean_dec(v___x_1210_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1219_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1227_, lean_object* v_bi_1228_, lean_object* v_type_1229_, lean_object* v_k_1230_, lean_object* v_kind_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v_bi_boxed_1237_; uint8_t v_kind_boxed_1238_; lean_object* v_res_1239_; 
v_bi_boxed_1237_ = lean_unbox(v_bi_1228_);
v_kind_boxed_1238_ = lean_unbox(v_kind_1231_);
v_res_1239_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1227_, v_bi_boxed_1237_, v_type_1229_, v_k_1230_, v_kind_boxed_1238_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(lean_object* v_name_1240_, lean_object* v_type_1241_, lean_object* v_k_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
uint8_t v___x_1248_; uint8_t v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = 0;
v___x_1249_ = 0;
v___x_1250_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1240_, v___x_1248_, v_type_1241_, v_k_1242_, v___x_1249_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1251_, lean_object* v_type_1252_, lean_object* v_k_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_1251_, v_type_1252_, v_k_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(lean_object* v_env_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v___x_1264_; lean_object* v_nextMacroScope_1265_; lean_object* v_ngen_1266_; lean_object* v_auxDeclNGen_1267_; lean_object* v_traceState_1268_; lean_object* v_messages_1269_; lean_object* v_infoState_1270_; lean_object* v_snapshotTasks_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1297_; 
v___x_1264_ = lean_st_ref_take(v___y_1262_);
v_nextMacroScope_1265_ = lean_ctor_get(v___x_1264_, 1);
v_ngen_1266_ = lean_ctor_get(v___x_1264_, 2);
v_auxDeclNGen_1267_ = lean_ctor_get(v___x_1264_, 3);
v_traceState_1268_ = lean_ctor_get(v___x_1264_, 4);
v_messages_1269_ = lean_ctor_get(v___x_1264_, 6);
v_infoState_1270_ = lean_ctor_get(v___x_1264_, 7);
v_snapshotTasks_1271_ = lean_ctor_get(v___x_1264_, 8);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1264_);
if (v_isSharedCheck_1297_ == 0)
{
lean_object* v_unused_1298_; lean_object* v_unused_1299_; 
v_unused_1298_ = lean_ctor_get(v___x_1264_, 5);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v___x_1264_, 0);
lean_dec(v_unused_1299_);
v___x_1273_ = v___x_1264_;
v_isShared_1274_ = v_isSharedCheck_1297_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snapshotTasks_1271_);
lean_inc(v_infoState_1270_);
lean_inc(v_messages_1269_);
lean_inc(v_traceState_1268_);
lean_inc(v_auxDeclNGen_1267_);
lean_inc(v_ngen_1266_);
lean_inc(v_nextMacroScope_1265_);
lean_dec(v___x_1264_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1297_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 5, v___x_1275_);
lean_ctor_set(v___x_1273_, 0, v_env_1260_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_env_1260_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_nextMacroScope_1265_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_ngen_1266_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v_auxDeclNGen_1267_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_traceState_1268_);
lean_ctor_set(v_reuseFailAlloc_1296_, 5, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1296_, 6, v_messages_1269_);
lean_ctor_set(v_reuseFailAlloc_1296_, 7, v_infoState_1270_);
lean_ctor_set(v_reuseFailAlloc_1296_, 8, v_snapshotTasks_1271_);
v___x_1277_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_mctx_1280_; lean_object* v_zetaDeltaFVarIds_1281_; lean_object* v_postponed_1282_; lean_object* v_diag_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1294_; 
v___x_1278_ = lean_st_ref_set(v___y_1262_, v___x_1277_);
v___x_1279_ = lean_st_ref_take(v___y_1261_);
v_mctx_1280_ = lean_ctor_get(v___x_1279_, 0);
v_zetaDeltaFVarIds_1281_ = lean_ctor_get(v___x_1279_, 2);
v_postponed_1282_ = lean_ctor_get(v___x_1279_, 3);
v_diag_1283_ = lean_ctor_get(v___x_1279_, 4);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1294_ == 0)
{
lean_object* v_unused_1295_; 
v_unused_1295_ = lean_ctor_get(v___x_1279_, 1);
lean_dec(v_unused_1295_);
v___x_1285_ = v___x_1279_;
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_diag_1283_);
lean_inc(v_postponed_1282_);
lean_inc(v_zetaDeltaFVarIds_1281_);
lean_inc(v_mctx_1280_);
lean_dec(v___x_1279_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1294_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1287_; lean_object* v___x_1289_; 
v___x_1287_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1287_);
v___x_1289_ = v___x_1285_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_mctx_1280_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_zetaDeltaFVarIds_1281_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v_postponed_1282_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_diag_1283_);
v___x_1289_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_st_ref_set(v___y_1261_, v___x_1289_);
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1291_);
return v___x_1292_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object* v_env_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_1300_, v___y_1301_, v___y_1302_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(lean_object* v_declName_1305_, lean_object* v_entry_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_){
_start:
{
lean_object* v___x_1312_; lean_object* v_env_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1312_ = lean_st_ref_get(v___y_1310_);
v_env_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc_ref(v_env_1313_);
lean_dec(v___x_1312_);
v___x_1314_ = l_Lean_Linter_deprecatedAttr;
v___x_1315_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1314_, v_env_1313_, v_declName_1305_, v_entry_1306_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1325_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1325_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1325_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set_tag(v___x_1318_, 3);
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
v___x_1322_ = l_Lean_MessageData_ofFormat(v___x_1321_);
v___x_1323_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_1322_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
return v___x_1323_;
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1327_; 
v_a_1326_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1326_);
lean_dec_ref(v___x_1315_);
v___x_1327_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_a_1326_, v___y_1308_, v___y_1310_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(lean_object* v_declName_1328_, lean_object* v_entry_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v_declName_1328_, v_entry_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(lean_object* v_declName_1336_, uint8_t v_s_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_){
_start:
{
lean_object* v___x_1341_; lean_object* v_env_1342_; lean_object* v_nextMacroScope_1343_; lean_object* v_ngen_1344_; lean_object* v_auxDeclNGen_1345_; lean_object* v_traceState_1346_; lean_object* v_messages_1347_; lean_object* v_infoState_1348_; lean_object* v_snapshotTasks_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1378_; 
v___x_1341_ = lean_st_ref_take(v___y_1339_);
v_env_1342_ = lean_ctor_get(v___x_1341_, 0);
v_nextMacroScope_1343_ = lean_ctor_get(v___x_1341_, 1);
v_ngen_1344_ = lean_ctor_get(v___x_1341_, 2);
v_auxDeclNGen_1345_ = lean_ctor_get(v___x_1341_, 3);
v_traceState_1346_ = lean_ctor_get(v___x_1341_, 4);
v_messages_1347_ = lean_ctor_get(v___x_1341_, 6);
v_infoState_1348_ = lean_ctor_get(v___x_1341_, 7);
v_snapshotTasks_1349_ = lean_ctor_get(v___x_1341_, 8);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v___x_1341_, 5);
lean_dec(v_unused_1379_);
v___x_1351_ = v___x_1341_;
v_isShared_1352_ = v_isSharedCheck_1378_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_snapshotTasks_1349_);
lean_inc(v_infoState_1348_);
lean_inc(v_messages_1347_);
lean_inc(v_traceState_1346_);
lean_inc(v_auxDeclNGen_1345_);
lean_inc(v_ngen_1344_);
lean_inc(v_nextMacroScope_1343_);
lean_inc(v_env_1342_);
lean_dec(v___x_1341_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1378_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
uint8_t v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1353_ = 0;
v___x_1354_ = lean_box(0);
v___x_1355_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1342_, v_declName_1336_, v_s_1337_, v___x_1353_, v___x_1354_);
v___x_1356_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1352_ == 0)
{
lean_ctor_set(v___x_1351_, 5, v___x_1356_);
lean_ctor_set(v___x_1351_, 0, v___x_1355_);
v___x_1358_ = v___x_1351_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_nextMacroScope_1343_);
lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_ngen_1344_);
lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_auxDeclNGen_1345_);
lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_traceState_1346_);
lean_ctor_set(v_reuseFailAlloc_1377_, 5, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1377_, 6, v_messages_1347_);
lean_ctor_set(v_reuseFailAlloc_1377_, 7, v_infoState_1348_);
lean_ctor_set(v_reuseFailAlloc_1377_, 8, v_snapshotTasks_1349_);
v___x_1358_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_mctx_1361_; lean_object* v_zetaDeltaFVarIds_1362_; lean_object* v_postponed_1363_; lean_object* v_diag_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1375_; 
v___x_1359_ = lean_st_ref_set(v___y_1339_, v___x_1358_);
v___x_1360_ = lean_st_ref_take(v___y_1338_);
v_mctx_1361_ = lean_ctor_get(v___x_1360_, 0);
v_zetaDeltaFVarIds_1362_ = lean_ctor_get(v___x_1360_, 2);
v_postponed_1363_ = lean_ctor_get(v___x_1360_, 3);
v_diag_1364_ = lean_ctor_get(v___x_1360_, 4);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1375_ == 0)
{
lean_object* v_unused_1376_; 
v_unused_1376_ = lean_ctor_get(v___x_1360_, 1);
lean_dec(v_unused_1376_);
v___x_1366_ = v___x_1360_;
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_diag_1364_);
lean_inc(v_postponed_1363_);
lean_inc(v_zetaDeltaFVarIds_1362_);
lean_inc(v_mctx_1361_);
lean_dec(v___x_1360_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1375_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 1, v___x_1368_);
v___x_1370_ = v___x_1366_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_mctx_1361_);
lean_ctor_set(v_reuseFailAlloc_1374_, 1, v___x_1368_);
lean_ctor_set(v_reuseFailAlloc_1374_, 2, v_zetaDeltaFVarIds_1362_);
lean_ctor_set(v_reuseFailAlloc_1374_, 3, v_postponed_1363_);
lean_ctor_set(v_reuseFailAlloc_1374_, 4, v_diag_1364_);
v___x_1370_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_st_ref_set(v___y_1338_, v___x_1370_);
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
return v___x_1373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object* v_declName_1380_, lean_object* v_s_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
uint8_t v_s_boxed_1385_; lean_object* v_res_1386_; 
v_s_boxed_1385_ = lean_unbox(v_s_1381_);
v_res_1386_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1380_, v_s_boxed_1385_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec(v___y_1382_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(lean_object* v_declName_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v___x_1393_; lean_object* v___x_1394_; 
v___x_1393_ = 0;
v___x_1394_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1387_, v___x_1393_, v___y_1389_, v___y_1391_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(lean_object* v_declName_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v_declName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1(lean_object* v___x_1408_, lean_object* v___x_1409_, lean_object* v_xs_1410_, uint8_t v___x_1411_, uint8_t v___x_1412_, lean_object* v_val_1413_, lean_object* v___x_1414_, lean_object* v___x_1415_, lean_object* v___x_1416_, lean_object* v___x_1417_, lean_object* v_ctors_1418_, lean_object* v___x_1419_, lean_object* v___x_1420_, lean_object* v_levelParams_1421_, lean_object* v_indName_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___x_1519_; 
lean_inc_ref(v___x_1409_);
lean_inc_ref(v___x_1408_);
v___x_1519_ = l_Lean_mkArrow(v___x_1408_, v___x_1409_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; 
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1519_);
v___x_1521_ = 1;
v___x_1522_ = l_Lean_Meta_mkForallFVars(v_xs_1410_, v_a_1520_, v___x_1411_, v___x_1412_, v___x_1412_, v___x_1521_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref(v___x_1522_);
v___x_1524_ = lean_box(v___x_1411_);
v___x_1525_ = lean_box(v___x_1412_);
v___x_1526_ = lean_box(v___x_1521_);
lean_inc(v___x_1415_);
lean_inc_ref(v_val_1413_);
v___f_1527_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1527_, 0, v_xs_1410_);
lean_closure_set(v___f_1527_, 1, v___x_1524_);
lean_closure_set(v___f_1527_, 2, v___x_1525_);
lean_closure_set(v___f_1527_, 3, v___x_1526_);
lean_closure_set(v___f_1527_, 4, v_val_1413_);
lean_closure_set(v___f_1527_, 5, v___x_1414_);
lean_closure_set(v___f_1527_, 6, v___x_1409_);
lean_closure_set(v___f_1527_, 7, v___x_1415_);
lean_closure_set(v___f_1527_, 8, v___x_1416_);
lean_closure_set(v___f_1527_, 9, v___x_1417_);
lean_closure_set(v___f_1527_, 10, v_ctors_1418_);
lean_closure_set(v___f_1527_, 11, v___x_1419_);
v___x_1528_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__3));
v___x_1529_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v___x_1528_, v___x_1408_, v___f_1527_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; lean_object* v___x_1531_; lean_object* v_env_1532_; uint32_t v___x_1533_; uint32_t v___x_1534_; uint32_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1739_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc_n(v_a_1530_, 2);
lean_dec_ref(v___x_1529_);
v___x_1531_ = lean_st_ref_get(v___y_1426_);
v_env_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc_ref(v_env_1532_);
lean_dec(v___x_1531_);
v___x_1533_ = l_Lean_getMaxHeight(v_env_1532_, v_a_1530_);
v___x_1534_ = 1;
v___x_1535_ = lean_uint32_add(v___x_1533_, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1536_, 0, v___x_1535_);
lean_inc(v_a_1523_);
lean_inc(v_levelParams_1421_);
lean_inc(v___x_1420_);
v___x_1537_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1420_, v_levelParams_1421_, v_a_1523_, v_a_1530_, v___x_1536_, v___y_1426_);
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1739_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1739_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
lean_object* v___y_1545_; lean_object* v___y_1546_; lean_object* v___y_1547_; lean_object* v___y_1548_; lean_object* v___y_1622_; lean_object* v___y_1623_; lean_object* v___y_1624_; lean_object* v___y_1625_; lean_object* v___x_1664_; 
lean_inc_ref(v___x_1543_);
v___x_1664_ = l_Lean_addDecl(v___x_1543_, v___x_1411_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v___x_1665_; lean_object* v_env_1666_; lean_object* v_nextMacroScope_1667_; lean_object* v_ngen_1668_; lean_object* v_auxDeclNGen_1669_; lean_object* v_traceState_1670_; lean_object* v_messages_1671_; lean_object* v_infoState_1672_; lean_object* v_snapshotTasks_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v___x_1664_);
v___x_1665_ = lean_st_ref_take(v___y_1426_);
v_env_1666_ = lean_ctor_get(v___x_1665_, 0);
v_nextMacroScope_1667_ = lean_ctor_get(v___x_1665_, 1);
v_ngen_1668_ = lean_ctor_get(v___x_1665_, 2);
v_auxDeclNGen_1669_ = lean_ctor_get(v___x_1665_, 3);
v_traceState_1670_ = lean_ctor_get(v___x_1665_, 4);
v_messages_1671_ = lean_ctor_get(v___x_1665_, 6);
v_infoState_1672_ = lean_ctor_get(v___x_1665_, 7);
v_snapshotTasks_1673_ = lean_ctor_get(v___x_1665_, 8);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1665_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1665_, 5);
lean_dec(v_unused_1737_);
v___x_1675_ = v___x_1665_;
v_isShared_1676_ = v_isSharedCheck_1736_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_snapshotTasks_1673_);
lean_inc(v_infoState_1672_);
lean_inc(v_messages_1671_);
lean_inc(v_traceState_1670_);
lean_inc(v_auxDeclNGen_1669_);
lean_inc(v_ngen_1668_);
lean_inc(v_nextMacroScope_1667_);
lean_inc(v_env_1666_);
lean_dec(v___x_1665_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1736_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_inc(v___x_1420_);
v___x_1677_ = l_Lean_Meta_addToCompletionBlackList(v_env_1666_, v___x_1420_);
v___x_1678_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 5, v___x_1678_);
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_nextMacroScope_1667_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v_ngen_1668_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_auxDeclNGen_1669_);
lean_ctor_set(v_reuseFailAlloc_1735_, 4, v_traceState_1670_);
lean_ctor_set(v_reuseFailAlloc_1735_, 5, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1735_, 6, v_messages_1671_);
lean_ctor_set(v_reuseFailAlloc_1735_, 7, v_infoState_1672_);
lean_ctor_set(v_reuseFailAlloc_1735_, 8, v_snapshotTasks_1673_);
v___x_1680_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_mctx_1683_; lean_object* v_zetaDeltaFVarIds_1684_; lean_object* v_postponed_1685_; lean_object* v_diag_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1733_; 
v___x_1681_ = lean_st_ref_set(v___y_1426_, v___x_1680_);
v___x_1682_ = lean_st_ref_take(v___y_1424_);
v_mctx_1683_ = lean_ctor_get(v___x_1682_, 0);
v_zetaDeltaFVarIds_1684_ = lean_ctor_get(v___x_1682_, 2);
v_postponed_1685_ = lean_ctor_get(v___x_1682_, 3);
v_diag_1686_ = lean_ctor_get(v___x_1682_, 4);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1682_, 1);
lean_dec(v_unused_1734_);
v___x_1688_ = v___x_1682_;
v_isShared_1689_ = v_isSharedCheck_1733_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_diag_1686_);
lean_inc(v_postponed_1685_);
lean_inc(v_zetaDeltaFVarIds_1684_);
lean_inc(v_mctx_1683_);
lean_dec(v___x_1682_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1733_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 1, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_mctx_1683_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_zetaDeltaFVarIds_1684_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_postponed_1685_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_diag_1686_);
v___x_1692_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v_env_1695_; lean_object* v_nextMacroScope_1696_; lean_object* v_ngen_1697_; lean_object* v_auxDeclNGen_1698_; lean_object* v_traceState_1699_; lean_object* v_messages_1700_; lean_object* v_infoState_1701_; lean_object* v_snapshotTasks_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1730_; 
v___x_1693_ = lean_st_ref_set(v___y_1424_, v___x_1692_);
v___x_1694_ = lean_st_ref_take(v___y_1426_);
v_env_1695_ = lean_ctor_get(v___x_1694_, 0);
v_nextMacroScope_1696_ = lean_ctor_get(v___x_1694_, 1);
v_ngen_1697_ = lean_ctor_get(v___x_1694_, 2);
v_auxDeclNGen_1698_ = lean_ctor_get(v___x_1694_, 3);
v_traceState_1699_ = lean_ctor_get(v___x_1694_, 4);
v_messages_1700_ = lean_ctor_get(v___x_1694_, 6);
v_infoState_1701_ = lean_ctor_get(v___x_1694_, 7);
v_snapshotTasks_1702_ = lean_ctor_get(v___x_1694_, 8);
v_isSharedCheck_1730_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1730_ == 0)
{
lean_object* v_unused_1731_; 
v_unused_1731_ = lean_ctor_get(v___x_1694_, 5);
lean_dec(v_unused_1731_);
v___x_1704_ = v___x_1694_;
v_isShared_1705_ = v_isSharedCheck_1730_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_snapshotTasks_1702_);
lean_inc(v_infoState_1701_);
lean_inc(v_messages_1700_);
lean_inc(v_traceState_1699_);
lean_inc(v_auxDeclNGen_1698_);
lean_inc(v_ngen_1697_);
lean_inc(v_nextMacroScope_1696_);
lean_inc(v_env_1695_);
lean_dec(v___x_1694_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1730_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
lean_inc(v___x_1420_);
v___x_1706_ = l_Lean_addProtected(v_env_1695_, v___x_1420_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 5, v___x_1678_);
lean_ctor_set(v___x_1704_, 0, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1706_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_nextMacroScope_1696_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v_ngen_1697_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_auxDeclNGen_1698_);
lean_ctor_set(v_reuseFailAlloc_1729_, 4, v_traceState_1699_);
lean_ctor_set(v_reuseFailAlloc_1729_, 5, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1729_, 6, v_messages_1700_);
lean_ctor_set(v_reuseFailAlloc_1729_, 7, v_infoState_1701_);
lean_ctor_set(v_reuseFailAlloc_1729_, 8, v_snapshotTasks_1702_);
v___x_1708_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v_mctx_1711_; lean_object* v_zetaDeltaFVarIds_1712_; lean_object* v_postponed_1713_; lean_object* v_diag_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1727_; 
v___x_1709_ = lean_st_ref_set(v___y_1426_, v___x_1708_);
v___x_1710_ = lean_st_ref_take(v___y_1424_);
v_mctx_1711_ = lean_ctor_get(v___x_1710_, 0);
v_zetaDeltaFVarIds_1712_ = lean_ctor_get(v___x_1710_, 2);
v_postponed_1713_ = lean_ctor_get(v___x_1710_, 3);
v_diag_1714_ = lean_ctor_get(v___x_1710_, 4);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v___x_1710_, 1);
lean_dec(v_unused_1728_);
v___x_1716_ = v___x_1710_;
v_isShared_1717_ = v_isSharedCheck_1727_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_diag_1714_);
lean_inc(v_postponed_1713_);
lean_inc(v_zetaDeltaFVarIds_1712_);
lean_inc(v_mctx_1711_);
lean_dec(v___x_1710_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1727_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1719_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 1, v___x_1690_);
v___x_1719_ = v___x_1716_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_mctx_1711_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_zetaDeltaFVarIds_1712_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_postponed_1713_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_diag_1714_);
v___x_1719_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1720_ = lean_st_ref_set(v___y_1424_, v___x_1719_);
v___x_1721_ = lean_unsigned_to_nat(1u);
v___x_1722_ = l_Lean_InductiveVal_numCtors(v_val_1413_);
lean_dec_ref(v_val_1413_);
v___x_1723_ = lean_nat_dec_eq(v___x_1722_, v___x_1721_);
lean_dec(v___x_1722_);
if (v___x_1723_ == 0)
{
v___y_1622_ = v___y_1423_;
v___y_1623_ = v___y_1424_;
v___y_1624_ = v___y_1425_;
v___y_1625_ = v___y_1426_;
goto v___jp_1621_;
}
else
{
uint8_t v___x_1724_; lean_object* v___x_1725_; 
v___x_1724_ = 2;
lean_inc(v___x_1420_);
v___x_1725_ = l_Lean_Meta_setInlineAttribute(v___x_1420_, v___x_1724_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_dec_ref(v___x_1725_);
v___y_1622_ = v___y_1423_;
v___y_1623_ = v___y_1424_;
v___y_1624_ = v___y_1425_;
v___y_1625_ = v___y_1426_;
goto v___jp_1621_;
}
else
{
lean_dec_ref(v___x_1543_);
lean_dec(v_a_1523_);
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1415_);
return v___x_1725_;
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
lean_dec_ref(v___x_1543_);
lean_dec(v_a_1523_);
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1415_);
lean_dec_ref(v_val_1413_);
return v___x_1664_;
}
v___jp_1544_:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_compileDecl(v___x_1543_, v___x_1412_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v___x_1550_; 
lean_dec_ref(v___x_1549_);
lean_inc(v___x_1420_);
v___x_1550_ = l_Lean_enableRealizationsForConst(v___x_1420_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v___x_1551_; 
lean_dec_ref(v___x_1550_);
lean_inc(v_indName_1422_);
v___x_1551_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_indName_1422_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1612_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1554_ = v___x_1551_;
v_isShared_1555_ = v_isSharedCheck_1612_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1551_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1612_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
uint8_t v___x_1556_; 
v___x_1556_ = lean_unbox(v_a_1552_);
lean_dec(v_a_1552_);
if (v___x_1556_ == 0)
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
lean_dec(v_a_1523_);
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1415_);
v___x_1557_ = lean_box(0);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v___x_1557_);
v___x_1559_ = v___x_1554_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
else
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1611_; 
lean_del_object(v___x_1554_);
lean_inc(v_indName_1422_);
v___x_1561_ = l_mkToCtorIdxName(v_indName_1422_);
lean_inc(v___x_1420_);
v___x_1562_ = l_Lean_mkConst(v___x_1420_, v___x_1415_);
v___x_1563_ = lean_box(1);
lean_inc(v___x_1561_);
v___x_1564_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1561_, v_levelParams_1421_, v_a_1523_, v___x_1562_, v___x_1563_, v___y_1548_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1611_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1611_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 1);
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_addDecl(v___x_1570_, v___x_1411_, v___y_1547_, v___y_1548_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v___x_1572_; lean_object* v_env_1573_; uint8_t v___x_1574_; 
lean_dec_ref(v___x_1571_);
v___x_1572_ = lean_st_ref_get(v___y_1548_);
v_env_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_ref(v_env_1573_);
lean_dec(v___x_1572_);
v___x_1574_ = l_Lean_isMarkedMeta(v_env_1573_, v_indName_1422_);
if (v___x_1574_ == 0)
{
v___y_1429_ = v___x_1561_;
v___y_1430_ = v___y_1545_;
v___y_1431_ = v___y_1546_;
v___y_1432_ = v___y_1547_;
v___y_1433_ = v___y_1548_;
goto v___jp_1428_;
}
else
{
lean_object* v___x_1575_; lean_object* v_env_1576_; lean_object* v_nextMacroScope_1577_; lean_object* v_ngen_1578_; lean_object* v_auxDeclNGen_1579_; lean_object* v_traceState_1580_; lean_object* v_messages_1581_; lean_object* v_infoState_1582_; lean_object* v_snapshotTasks_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1608_; 
v___x_1575_ = lean_st_ref_take(v___y_1548_);
v_env_1576_ = lean_ctor_get(v___x_1575_, 0);
v_nextMacroScope_1577_ = lean_ctor_get(v___x_1575_, 1);
v_ngen_1578_ = lean_ctor_get(v___x_1575_, 2);
v_auxDeclNGen_1579_ = lean_ctor_get(v___x_1575_, 3);
v_traceState_1580_ = lean_ctor_get(v___x_1575_, 4);
v_messages_1581_ = lean_ctor_get(v___x_1575_, 6);
v_infoState_1582_ = lean_ctor_get(v___x_1575_, 7);
v_snapshotTasks_1583_ = lean_ctor_get(v___x_1575_, 8);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; 
v_unused_1609_ = lean_ctor_get(v___x_1575_, 5);
lean_dec(v_unused_1609_);
v___x_1585_ = v___x_1575_;
v_isShared_1586_ = v_isSharedCheck_1608_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_snapshotTasks_1583_);
lean_inc(v_infoState_1582_);
lean_inc(v_messages_1581_);
lean_inc(v_traceState_1580_);
lean_inc(v_auxDeclNGen_1579_);
lean_inc(v_ngen_1578_);
lean_inc(v_nextMacroScope_1577_);
lean_inc(v_env_1576_);
lean_dec(v___x_1575_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1608_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
lean_inc(v___x_1561_);
v___x_1587_ = l_Lean_markMeta(v_env_1576_, v___x_1561_);
v___x_1588_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 5, v___x_1588_);
lean_ctor_set(v___x_1585_, 0, v___x_1587_);
v___x_1590_ = v___x_1585_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_nextMacroScope_1577_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_ngen_1578_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_auxDeclNGen_1579_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_traceState_1580_);
lean_ctor_set(v_reuseFailAlloc_1607_, 5, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1607_, 6, v_messages_1581_);
lean_ctor_set(v_reuseFailAlloc_1607_, 7, v_infoState_1582_);
lean_ctor_set(v_reuseFailAlloc_1607_, 8, v_snapshotTasks_1583_);
v___x_1590_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v_mctx_1593_; lean_object* v_zetaDeltaFVarIds_1594_; lean_object* v_postponed_1595_; lean_object* v_diag_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1605_; 
v___x_1591_ = lean_st_ref_set(v___y_1548_, v___x_1590_);
v___x_1592_ = lean_st_ref_take(v___y_1546_);
v_mctx_1593_ = lean_ctor_get(v___x_1592_, 0);
v_zetaDeltaFVarIds_1594_ = lean_ctor_get(v___x_1592_, 2);
v_postponed_1595_ = lean_ctor_get(v___x_1592_, 3);
v_diag_1596_ = lean_ctor_get(v___x_1592_, 4);
v_isSharedCheck_1605_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v___x_1592_, 1);
lean_dec(v_unused_1606_);
v___x_1598_ = v___x_1592_;
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_diag_1596_);
lean_inc(v_postponed_1595_);
lean_inc(v_zetaDeltaFVarIds_1594_);
lean_inc(v_mctx_1593_);
lean_dec(v___x_1592_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1600_);
v___x_1602_ = v___x_1598_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_mctx_1593_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_zetaDeltaFVarIds_1594_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_postponed_1595_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_diag_1596_);
v___x_1602_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_st_ref_set(v___y_1546_, v___x_1602_);
v___y_1429_ = v___x_1561_;
v___y_1430_ = v___y_1545_;
v___y_1431_ = v___y_1546_;
v___y_1432_ = v___y_1547_;
v___y_1433_ = v___y_1548_;
goto v___jp_1428_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1561_);
lean_dec(v_indName_1422_);
lean_dec(v___x_1420_);
return v___x_1571_;
}
}
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec(v_a_1523_);
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1415_);
v_a_1613_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1551_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1551_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_dec(v_a_1523_);
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1415_);
return v___x_1550_;
}
}
else
{
lean_dec(v_a_1523_);
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1415_);
return v___x_1549_;
}
}
v___jp_1621_:
{
lean_object* v___x_1626_; lean_object* v_env_1627_; uint8_t v___x_1628_; 
v___x_1626_ = lean_st_ref_get(v___y_1625_);
v_env_1627_ = lean_ctor_get(v___x_1626_, 0);
lean_inc_ref(v_env_1627_);
lean_dec(v___x_1626_);
lean_inc(v_indName_1422_);
v___x_1628_ = l_Lean_isMarkedMeta(v_env_1627_, v_indName_1422_);
if (v___x_1628_ == 0)
{
v___y_1545_ = v___y_1622_;
v___y_1546_ = v___y_1623_;
v___y_1547_ = v___y_1624_;
v___y_1548_ = v___y_1625_;
goto v___jp_1544_;
}
else
{
lean_object* v___x_1629_; lean_object* v_env_1630_; lean_object* v_nextMacroScope_1631_; lean_object* v_ngen_1632_; lean_object* v_auxDeclNGen_1633_; lean_object* v_traceState_1634_; lean_object* v_messages_1635_; lean_object* v_infoState_1636_; lean_object* v_snapshotTasks_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1662_; 
v___x_1629_ = lean_st_ref_take(v___y_1625_);
v_env_1630_ = lean_ctor_get(v___x_1629_, 0);
v_nextMacroScope_1631_ = lean_ctor_get(v___x_1629_, 1);
v_ngen_1632_ = lean_ctor_get(v___x_1629_, 2);
v_auxDeclNGen_1633_ = lean_ctor_get(v___x_1629_, 3);
v_traceState_1634_ = lean_ctor_get(v___x_1629_, 4);
v_messages_1635_ = lean_ctor_get(v___x_1629_, 6);
v_infoState_1636_ = lean_ctor_get(v___x_1629_, 7);
v_snapshotTasks_1637_ = lean_ctor_get(v___x_1629_, 8);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1662_ == 0)
{
lean_object* v_unused_1663_; 
v_unused_1663_ = lean_ctor_get(v___x_1629_, 5);
lean_dec(v_unused_1663_);
v___x_1639_ = v___x_1629_;
v_isShared_1640_ = v_isSharedCheck_1662_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_snapshotTasks_1637_);
lean_inc(v_infoState_1636_);
lean_inc(v_messages_1635_);
lean_inc(v_traceState_1634_);
lean_inc(v_auxDeclNGen_1633_);
lean_inc(v_ngen_1632_);
lean_inc(v_nextMacroScope_1631_);
lean_inc(v_env_1630_);
lean_dec(v___x_1629_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1662_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
lean_inc(v___x_1420_);
v___x_1641_ = l_Lean_markMeta(v_env_1630_, v___x_1420_);
v___x_1642_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 5, v___x_1642_);
lean_ctor_set(v___x_1639_, 0, v___x_1641_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_nextMacroScope_1631_);
lean_ctor_set(v_reuseFailAlloc_1661_, 2, v_ngen_1632_);
lean_ctor_set(v_reuseFailAlloc_1661_, 3, v_auxDeclNGen_1633_);
lean_ctor_set(v_reuseFailAlloc_1661_, 4, v_traceState_1634_);
lean_ctor_set(v_reuseFailAlloc_1661_, 5, v___x_1642_);
lean_ctor_set(v_reuseFailAlloc_1661_, 6, v_messages_1635_);
lean_ctor_set(v_reuseFailAlloc_1661_, 7, v_infoState_1636_);
lean_ctor_set(v_reuseFailAlloc_1661_, 8, v_snapshotTasks_1637_);
v___x_1644_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v_mctx_1647_; lean_object* v_zetaDeltaFVarIds_1648_; lean_object* v_postponed_1649_; lean_object* v_diag_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1659_; 
v___x_1645_ = lean_st_ref_set(v___y_1625_, v___x_1644_);
v___x_1646_ = lean_st_ref_take(v___y_1623_);
v_mctx_1647_ = lean_ctor_get(v___x_1646_, 0);
v_zetaDeltaFVarIds_1648_ = lean_ctor_get(v___x_1646_, 2);
v_postponed_1649_ = lean_ctor_get(v___x_1646_, 3);
v_diag_1650_ = lean_ctor_get(v___x_1646_, 4);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v___x_1646_, 1);
lean_dec(v_unused_1660_);
v___x_1652_ = v___x_1646_;
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_diag_1650_);
lean_inc(v_postponed_1649_);
lean_inc(v_zetaDeltaFVarIds_1648_);
lean_inc(v_mctx_1647_);
lean_dec(v___x_1646_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1659_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1654_; lean_object* v___x_1656_; 
v___x_1654_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1653_ == 0)
{
lean_ctor_set(v___x_1652_, 1, v___x_1654_);
v___x_1656_ = v___x_1652_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_mctx_1647_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1654_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_zetaDeltaFVarIds_1648_);
lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_postponed_1649_);
lean_ctor_set(v_reuseFailAlloc_1658_, 4, v_diag_1650_);
v___x_1656_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_st_ref_set(v___y_1623_, v___x_1656_);
v___y_1545_ = v___y_1622_;
v___y_1546_ = v___y_1623_;
v___y_1547_ = v___y_1624_;
v___y_1548_ = v___y_1625_;
goto v___jp_1544_;
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
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_a_1523_);
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1415_);
lean_dec_ref(v_val_1413_);
v_a_1740_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1529_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1529_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1419_);
lean_dec(v_ctors_1418_);
lean_dec_ref(v___x_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_val_1413_);
lean_dec_ref(v_xs_1410_);
lean_dec_ref(v___x_1409_);
lean_dec_ref(v___x_1408_);
v_a_1748_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1522_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1522_);
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
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_indName_1422_);
lean_dec(v_levelParams_1421_);
lean_dec(v___x_1420_);
lean_dec(v___x_1419_);
lean_dec(v_ctors_1418_);
lean_dec_ref(v___x_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v_val_1413_);
lean_dec_ref(v_xs_1410_);
lean_dec_ref(v___x_1409_);
lean_dec_ref(v___x_1408_);
v_a_1756_ = lean_ctor_get(v___x_1519_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1519_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1519_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1519_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
v___jp_1428_:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1434_ = lean_unsigned_to_nat(1u);
v___x_1435_ = lean_mk_empty_array_with_capacity(v___x_1434_);
lean_inc(v___y_1429_);
v___x_1436_ = lean_array_push(v___x_1435_, v___y_1429_);
v___x_1437_ = l_Lean_compileDecls(v___x_1436_, v___x_1412_, v___y_1432_, v___y_1433_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1438_; lean_object* v_env_1439_; lean_object* v_nextMacroScope_1440_; lean_object* v_ngen_1441_; lean_object* v_auxDeclNGen_1442_; lean_object* v_traceState_1443_; lean_object* v_messages_1444_; lean_object* v_infoState_1445_; lean_object* v_snapshotTasks_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v___x_1437_);
v___x_1438_ = lean_st_ref_take(v___y_1433_);
v_env_1439_ = lean_ctor_get(v___x_1438_, 0);
v_nextMacroScope_1440_ = lean_ctor_get(v___x_1438_, 1);
v_ngen_1441_ = lean_ctor_get(v___x_1438_, 2);
v_auxDeclNGen_1442_ = lean_ctor_get(v___x_1438_, 3);
v_traceState_1443_ = lean_ctor_get(v___x_1438_, 4);
v_messages_1444_ = lean_ctor_get(v___x_1438_, 6);
v_infoState_1445_ = lean_ctor_get(v___x_1438_, 7);
v_snapshotTasks_1446_ = lean_ctor_get(v___x_1438_, 8);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1517_ == 0)
{
lean_object* v_unused_1518_; 
v_unused_1518_ = lean_ctor_get(v___x_1438_, 5);
lean_dec(v_unused_1518_);
v___x_1448_ = v___x_1438_;
v_isShared_1449_ = v_isSharedCheck_1517_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_snapshotTasks_1446_);
lean_inc(v_infoState_1445_);
lean_inc(v_messages_1444_);
lean_inc(v_traceState_1443_);
lean_inc(v_auxDeclNGen_1442_);
lean_inc(v_ngen_1441_);
lean_inc(v_nextMacroScope_1440_);
lean_inc(v_env_1439_);
lean_dec(v___x_1438_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1517_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1453_; 
lean_inc(v___y_1429_);
v___x_1450_ = l_Lean_Meta_addToCompletionBlackList(v_env_1439_, v___y_1429_);
v___x_1451_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 5, v___x_1451_);
lean_ctor_set(v___x_1448_, 0, v___x_1450_);
v___x_1453_ = v___x_1448_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1450_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v_nextMacroScope_1440_);
lean_ctor_set(v_reuseFailAlloc_1516_, 2, v_ngen_1441_);
lean_ctor_set(v_reuseFailAlloc_1516_, 3, v_auxDeclNGen_1442_);
lean_ctor_set(v_reuseFailAlloc_1516_, 4, v_traceState_1443_);
lean_ctor_set(v_reuseFailAlloc_1516_, 5, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1516_, 6, v_messages_1444_);
lean_ctor_set(v_reuseFailAlloc_1516_, 7, v_infoState_1445_);
lean_ctor_set(v_reuseFailAlloc_1516_, 8, v_snapshotTasks_1446_);
v___x_1453_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v_mctx_1456_; lean_object* v_zetaDeltaFVarIds_1457_; lean_object* v_postponed_1458_; lean_object* v_diag_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1514_; 
v___x_1454_ = lean_st_ref_set(v___y_1433_, v___x_1453_);
v___x_1455_ = lean_st_ref_take(v___y_1431_);
v_mctx_1456_ = lean_ctor_get(v___x_1455_, 0);
v_zetaDeltaFVarIds_1457_ = lean_ctor_get(v___x_1455_, 2);
v_postponed_1458_ = lean_ctor_get(v___x_1455_, 3);
v_diag_1459_ = lean_ctor_get(v___x_1455_, 4);
v_isSharedCheck_1514_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v___x_1455_, 1);
lean_dec(v_unused_1515_);
v___x_1461_ = v___x_1455_;
v_isShared_1462_ = v_isSharedCheck_1514_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_diag_1459_);
lean_inc(v_postponed_1458_);
lean_inc(v_zetaDeltaFVarIds_1457_);
lean_inc(v_mctx_1456_);
lean_dec(v___x_1455_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1514_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v___x_1465_; 
v___x_1463_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 1, v___x_1463_);
v___x_1465_ = v___x_1461_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v_mctx_1456_);
lean_ctor_set(v_reuseFailAlloc_1513_, 1, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_zetaDeltaFVarIds_1457_);
lean_ctor_set(v_reuseFailAlloc_1513_, 3, v_postponed_1458_);
lean_ctor_set(v_reuseFailAlloc_1513_, 4, v_diag_1459_);
v___x_1465_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v_env_1468_; lean_object* v_nextMacroScope_1469_; lean_object* v_ngen_1470_; lean_object* v_auxDeclNGen_1471_; lean_object* v_traceState_1472_; lean_object* v_messages_1473_; lean_object* v_infoState_1474_; lean_object* v_snapshotTasks_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1511_; 
v___x_1466_ = lean_st_ref_set(v___y_1431_, v___x_1465_);
v___x_1467_ = lean_st_ref_take(v___y_1433_);
v_env_1468_ = lean_ctor_get(v___x_1467_, 0);
v_nextMacroScope_1469_ = lean_ctor_get(v___x_1467_, 1);
v_ngen_1470_ = lean_ctor_get(v___x_1467_, 2);
v_auxDeclNGen_1471_ = lean_ctor_get(v___x_1467_, 3);
v_traceState_1472_ = lean_ctor_get(v___x_1467_, 4);
v_messages_1473_ = lean_ctor_get(v___x_1467_, 6);
v_infoState_1474_ = lean_ctor_get(v___x_1467_, 7);
v_snapshotTasks_1475_ = lean_ctor_get(v___x_1467_, 8);
v_isSharedCheck_1511_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; 
v_unused_1512_ = lean_ctor_get(v___x_1467_, 5);
lean_dec(v_unused_1512_);
v___x_1477_ = v___x_1467_;
v_isShared_1478_ = v_isSharedCheck_1511_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snapshotTasks_1475_);
lean_inc(v_infoState_1474_);
lean_inc(v_messages_1473_);
lean_inc(v_traceState_1472_);
lean_inc(v_auxDeclNGen_1471_);
lean_inc(v_ngen_1470_);
lean_inc(v_nextMacroScope_1469_);
lean_inc(v_env_1468_);
lean_dec(v___x_1467_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1511_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
lean_inc(v___y_1429_);
v___x_1479_ = l_Lean_addProtected(v_env_1468_, v___y_1429_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 5, v___x_1451_);
lean_ctor_set(v___x_1477_, 0, v___x_1479_);
v___x_1481_ = v___x_1477_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_nextMacroScope_1469_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v_ngen_1470_);
lean_ctor_set(v_reuseFailAlloc_1510_, 3, v_auxDeclNGen_1471_);
lean_ctor_set(v_reuseFailAlloc_1510_, 4, v_traceState_1472_);
lean_ctor_set(v_reuseFailAlloc_1510_, 5, v___x_1451_);
lean_ctor_set(v_reuseFailAlloc_1510_, 6, v_messages_1473_);
lean_ctor_set(v_reuseFailAlloc_1510_, 7, v_infoState_1474_);
lean_ctor_set(v_reuseFailAlloc_1510_, 8, v_snapshotTasks_1475_);
v___x_1481_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_mctx_1484_; lean_object* v_zetaDeltaFVarIds_1485_; lean_object* v_postponed_1486_; lean_object* v_diag_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1508_; 
v___x_1482_ = lean_st_ref_set(v___y_1433_, v___x_1481_);
v___x_1483_ = lean_st_ref_take(v___y_1431_);
v_mctx_1484_ = lean_ctor_get(v___x_1483_, 0);
v_zetaDeltaFVarIds_1485_ = lean_ctor_get(v___x_1483_, 2);
v_postponed_1486_ = lean_ctor_get(v___x_1483_, 3);
v_diag_1487_ = lean_ctor_get(v___x_1483_, 4);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v___x_1483_, 1);
lean_dec(v_unused_1509_);
v___x_1489_ = v___x_1483_;
v_isShared_1490_ = v_isSharedCheck_1508_;
goto v_resetjp_1488_;
}
else
{
lean_inc(v_diag_1487_);
lean_inc(v_postponed_1486_);
lean_inc(v_zetaDeltaFVarIds_1485_);
lean_inc(v_mctx_1484_);
lean_dec(v___x_1483_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1508_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1492_; 
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1463_);
v___x_1492_ = v___x_1489_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_mctx_1484_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1507_, 2, v_zetaDeltaFVarIds_1485_);
lean_ctor_set(v_reuseFailAlloc_1507_, 3, v_postponed_1486_);
lean_ctor_set(v_reuseFailAlloc_1507_, 4, v_diag_1487_);
v___x_1492_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1505_; 
v___x_1493_ = lean_st_ref_set(v___y_1431_, v___x_1492_);
lean_inc(v___y_1429_);
v___x_1494_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v___x_1494_, 0);
lean_dec(v_unused_1506_);
v___x_1496_ = v___x_1494_;
v_isShared_1497_ = v_isSharedCheck_1505_;
goto v_resetjp_1495_;
}
else
{
lean_dec(v___x_1494_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1505_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 1);
lean_ctor_set(v___x_1496_, 0, v___x_1420_);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1420_);
v___x_1499_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__1));
v___x_1502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1499_);
lean_ctor_set(v___x_1502_, 1, v___x_1500_);
lean_ctor_set(v___x_1502_, 2, v___x_1501_);
v___x_1503_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v___y_1429_, v___x_1502_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
return v___x_1503_;
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
lean_dec(v___y_1429_);
lean_dec(v___x_1420_);
return v___x_1437_;
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1764_ = _args[0];
lean_object* v___x_1765_ = _args[1];
lean_object* v_xs_1766_ = _args[2];
lean_object* v___x_1767_ = _args[3];
lean_object* v___x_1768_ = _args[4];
lean_object* v_val_1769_ = _args[5];
lean_object* v___x_1770_ = _args[6];
lean_object* v___x_1771_ = _args[7];
lean_object* v___x_1772_ = _args[8];
lean_object* v___x_1773_ = _args[9];
lean_object* v_ctors_1774_ = _args[10];
lean_object* v___x_1775_ = _args[11];
lean_object* v___x_1776_ = _args[12];
lean_object* v_levelParams_1777_ = _args[13];
lean_object* v_indName_1778_ = _args[14];
lean_object* v___y_1779_ = _args[15];
lean_object* v___y_1780_ = _args[16];
lean_object* v___y_1781_ = _args[17];
lean_object* v___y_1782_ = _args[18];
lean_object* v___y_1783_ = _args[19];
_start:
{
uint8_t v___x_36061__boxed_1784_; uint8_t v___x_36062__boxed_1785_; lean_object* v_res_1786_; 
v___x_36061__boxed_1784_ = lean_unbox(v___x_1767_);
v___x_36062__boxed_1785_ = lean_unbox(v___x_1768_);
v_res_1786_ = l_mkCtorIdx___lam__1(v___x_1764_, v___x_1765_, v_xs_1766_, v___x_36061__boxed_1784_, v___x_36062__boxed_1785_, v_val_1769_, v___x_1770_, v___x_1771_, v___x_1772_, v___x_1773_, v_ctors_1774_, v___x_1775_, v___x_1776_, v_levelParams_1777_, v_indName_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(lean_object* v_bs_1787_, lean_object* v_k_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1787_, v_k_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1794_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1794_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
else
{
lean_object* v_a_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_a_1803_ = lean_ctor_get(v___x_1794_, 0);
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1805_ = v___x_1794_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_a_1803_);
lean_dec(v___x_1794_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v_a_1803_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object* v_bs_1811_, lean_object* v_k_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_1811_, v_k_1812_, v___y_1813_, v___y_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec_ref(v_bs_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(size_t v_sz_1819_, size_t v_i_1820_, lean_object* v_bs_1821_){
_start:
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_usize_dec_lt(v_i_1820_, v_sz_1819_);
if (v___x_1822_ == 0)
{
return v_bs_1821_;
}
else
{
lean_object* v_v_1823_; lean_object* v___x_1824_; lean_object* v_bs_x27_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v_v_1823_ = lean_array_uget(v_bs_1821_, v_i_1820_);
v___x_1824_ = lean_unsigned_to_nat(0u);
v_bs_x27_1825_ = lean_array_uset(v_bs_1821_, v_i_1820_, v___x_1824_);
v___x_1826_ = l_Lean_Expr_fvarId_x21(v_v_1823_);
lean_dec(v_v_1823_);
v___x_1827_ = 1;
v___x_1828_ = lean_box(v___x_1827_);
v___x_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1829_, 0, v___x_1826_);
lean_ctor_set(v___x_1829_, 1, v___x_1828_);
v___x_1830_ = ((size_t)1ULL);
v___x_1831_ = lean_usize_add(v_i_1820_, v___x_1830_);
v___x_1832_ = lean_array_uset(v_bs_x27_1825_, v_i_1820_, v___x_1829_);
v_i_1820_ = v___x_1831_;
v_bs_1821_ = v___x_1832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(lean_object* v_sz_1834_, lean_object* v_i_1835_, lean_object* v_bs_1836_){
_start:
{
size_t v_sz_boxed_1837_; size_t v_i_boxed_1838_; lean_object* v_res_1839_; 
v_sz_boxed_1837_ = lean_unbox_usize(v_sz_1834_);
lean_dec(v_sz_1834_);
v_i_boxed_1838_ = lean_unbox_usize(v_i_1835_);
lean_dec(v_i_1835_);
v_res_1839_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_boxed_1837_, v_i_boxed_1838_, v_bs_1836_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(lean_object* v_bs_1840_, lean_object* v_k_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
size_t v_sz_1847_; size_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_sz_1847_ = lean_array_size(v_bs_1840_);
v___x_1848_ = ((size_t)0ULL);
v___x_1849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_1847_, v___x_1848_, v_bs_1840_);
v___x_1850_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v___x_1849_, v_k_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec_ref(v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(lean_object* v_bs_1851_, lean_object* v_k_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_1851_, v_k_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2(lean_object* v_numParams_1862_, lean_object* v_indName_1863_, lean_object* v___x_1864_, lean_object* v___x_1865_, uint8_t v___x_1866_, uint8_t v___x_1867_, lean_object* v_val_1868_, lean_object* v___x_1869_, lean_object* v_ctors_1870_, lean_object* v___x_1871_, lean_object* v_levelParams_1872_, lean_object* v_xs_1873_, lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___f_1892_; lean_object* v___x_1893_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1862_);
lean_inc_ref_n(v_xs_1873_, 3);
v___x_1881_ = l_Array_toSubarray___redArg(v_xs_1873_, v___x_1880_, v_numParams_1862_);
v___x_1882_ = l_Subarray_copy___redArg(v___x_1881_);
v___x_1883_ = lean_array_get_size(v_xs_1873_);
v___x_1884_ = l_Array_toSubarray___redArg(v_xs_1873_, v_numParams_1862_, v___x_1883_);
v___x_1885_ = l_Subarray_copy___redArg(v___x_1884_);
lean_inc(v___x_1864_);
lean_inc(v_indName_1863_);
v___x_1886_ = l_Lean_mkConst(v_indName_1863_, v___x_1864_);
v___x_1887_ = l_Lean_mkAppN(v___x_1886_, v_xs_1873_);
v___x_1888_ = ((lean_object*)(l_mkCtorIdx___lam__2___closed__1));
v___x_1889_ = l_Lean_mkConst(v___x_1888_, v___x_1865_);
v___x_1890_ = lean_box(v___x_1866_);
v___x_1891_ = lean_box(v___x_1867_);
v___f_1892_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1892_, 0, v___x_1887_);
lean_closure_set(v___f_1892_, 1, v___x_1889_);
lean_closure_set(v___f_1892_, 2, v_xs_1873_);
lean_closure_set(v___f_1892_, 3, v___x_1890_);
lean_closure_set(v___f_1892_, 4, v___x_1891_);
lean_closure_set(v___f_1892_, 5, v_val_1868_);
lean_closure_set(v___f_1892_, 6, v___x_1885_);
lean_closure_set(v___f_1892_, 7, v___x_1864_);
lean_closure_set(v___f_1892_, 8, v___x_1869_);
lean_closure_set(v___f_1892_, 9, v___x_1882_);
lean_closure_set(v___f_1892_, 10, v_ctors_1870_);
lean_closure_set(v___f_1892_, 11, v___x_1880_);
lean_closure_set(v___f_1892_, 12, v___x_1871_);
lean_closure_set(v___f_1892_, 13, v_levelParams_1872_);
lean_closure_set(v___f_1892_, 14, v_indName_1863_);
v___x_1893_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_xs_1873_, v___f_1892_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1894_ = _args[0];
lean_object* v_indName_1895_ = _args[1];
lean_object* v___x_1896_ = _args[2];
lean_object* v___x_1897_ = _args[3];
lean_object* v___x_1898_ = _args[4];
lean_object* v___x_1899_ = _args[5];
lean_object* v_val_1900_ = _args[6];
lean_object* v___x_1901_ = _args[7];
lean_object* v_ctors_1902_ = _args[8];
lean_object* v___x_1903_ = _args[9];
lean_object* v_levelParams_1904_ = _args[10];
lean_object* v_xs_1905_ = _args[11];
lean_object* v_x_1906_ = _args[12];
lean_object* v___y_1907_ = _args[13];
lean_object* v___y_1908_ = _args[14];
lean_object* v___y_1909_ = _args[15];
lean_object* v___y_1910_ = _args[16];
lean_object* v___y_1911_ = _args[17];
_start:
{
uint8_t v___x_36749__boxed_1912_; uint8_t v___x_36750__boxed_1913_; lean_object* v_res_1914_; 
v___x_36749__boxed_1912_ = lean_unbox(v___x_1898_);
v___x_36750__boxed_1913_ = lean_unbox(v___x_1899_);
v_res_1914_ = l_mkCtorIdx___lam__2(v_numParams_1894_, v_indName_1895_, v___x_1896_, v___x_1897_, v___x_36749__boxed_1912_, v___x_36750__boxed_1913_, v_val_1900_, v___x_1901_, v_ctors_1902_, v___x_1903_, v_levelParams_1904_, v_xs_1905_, v_x_1906_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
lean_dec(v___y_1910_);
lean_dec_ref(v___y_1909_);
lean_dec(v___y_1908_);
lean_dec_ref(v___y_1907_);
lean_dec_ref(v_x_1906_);
return v_res_1914_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00mkCtorIdx_spec__3(lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
if (lean_obj_tag(v_a_1915_) == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = l_List_reverse___redArg(v_a_1916_);
return v___x_1917_;
}
else
{
lean_object* v_head_1918_; lean_object* v_tail_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1928_; 
v_head_1918_ = lean_ctor_get(v_a_1915_, 0);
v_tail_1919_ = lean_ctor_get(v_a_1915_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_a_1915_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1921_ = v_a_1915_;
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_tail_1919_);
lean_inc(v_head_1918_);
lean_dec(v_a_1915_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1928_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = l_Lean_mkLevelParam(v_head_1918_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v_a_1916_);
lean_ctor_set(v___x_1921_, 0, v___x_1923_);
v___x_1925_ = v___x_1921_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1916_);
v___x_1925_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
v_a_1915_ = v_tail_1919_;
v_a_1916_ = v___x_1925_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1931_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_1932_ = lean_unsigned_to_nat(62u);
v___x_1933_ = lean_unsigned_to_nat(48u);
v___x_1934_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__1));
v___x_1935_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__0));
v___x_1936_ = l_mkPanicMessageWithDecl(v___x_1935_, v___x_1934_, v___x_1933_, v___x_1932_, v___x_1931_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3(lean_object* v_indName_1937_, uint8_t v___x_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_options_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v_options_1944_ = lean_ctor_get(v___y_1941_, 2);
v___x_1945_ = l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
v___x_1946_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_options_1944_, v___x_1945_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec(v_indName_1937_);
v___x_1947_ = lean_box(0);
v___x_1948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1948_, 0, v___x_1947_);
return v___x_1948_;
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_2035_; 
lean_inc(v_indName_1937_);
v___x_1949_ = l_mkCtorIdxName(v_indName_1937_);
lean_inc(v___x_1949_);
v___x_1950_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v___x_1949_, v___x_1946_, v___y_1942_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_2035_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_2035_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
uint8_t v___x_1955_; 
v___x_1955_ = lean_unbox(v_a_1951_);
lean_dec(v_a_1951_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; 
lean_del_object(v___x_1953_);
lean_inc(v_indName_1937_);
v___x_1956_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_indName_1937_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
if (lean_obj_tag(v_a_1957_) == 5)
{
lean_object* v_val_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_2020_; 
v_val_1958_ = lean_ctor_get(v_a_1957_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_a_1957_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_1960_ = v_a_1957_;
v_isShared_1961_ = v_isSharedCheck_2020_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_val_1958_);
lean_dec(v_a_1957_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_2020_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_toConstantVal_1962_; lean_object* v_numParams_1963_; lean_object* v_numIndices_1964_; lean_object* v_ctors_1965_; lean_object* v_levelParams_1966_; lean_object* v_type_1967_; lean_object* v___x_1968_; 
v_toConstantVal_1962_ = lean_ctor_get(v_val_1958_, 0);
v_numParams_1963_ = lean_ctor_get(v_val_1958_, 1);
lean_inc(v_numParams_1963_);
v_numIndices_1964_ = lean_ctor_get(v_val_1958_, 2);
lean_inc(v_numIndices_1964_);
v_ctors_1965_ = lean_ctor_get(v_val_1958_, 4);
lean_inc(v_ctors_1965_);
v_levelParams_1966_ = lean_ctor_get(v_toConstantVal_1962_, 1);
lean_inc(v_levelParams_1966_);
v_type_1967_ = lean_ctor_get(v_toConstantVal_1962_, 2);
lean_inc_ref_n(v_type_1967_, 2);
v___x_1968_ = l_Lean_Meta_isPropFormerType(v_type_1967_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v_a_1969_; lean_object* v___x_1971_; uint8_t v_isShared_1972_; uint8_t v_isSharedCheck_2011_; 
v_a_1969_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1971_ = v___x_1968_;
v_isShared_1972_ = v_isSharedCheck_2011_;
goto v_resetjp_1970_;
}
else
{
lean_inc(v_a_1969_);
lean_dec(v___x_1968_);
v___x_1971_ = lean_box(0);
v_isShared_1972_ = v_isSharedCheck_2011_;
goto v_resetjp_1970_;
}
v_resetjp_1970_:
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_unbox(v_a_1969_);
lean_dec(v_a_1969_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_del_object(v___x_1971_);
lean_inc(v_indName_1937_);
v___x_1974_ = l_Lean_mkCasesOnName(v_indName_1937_);
lean_inc(v___x_1974_);
v___x_1975_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v___x_1974_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1998_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1978_ = v___x_1975_;
v_isShared_1979_ = v_isSharedCheck_1998_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_a_1976_);
lean_dec(v___x_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1998_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1980_ = l_List_lengthTR___redArg(v_levelParams_1966_);
v___x_1981_ = l_Lean_ConstantInfo_levelParams(v_a_1976_);
lean_dec(v_a_1976_);
v___x_1982_ = l_List_lengthTR___redArg(v___x_1981_);
lean_dec(v___x_1981_);
v___x_1983_ = lean_nat_dec_lt(v___x_1980_, v___x_1982_);
lean_dec(v___x_1982_);
lean_dec(v___x_1980_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
lean_dec(v___x_1974_);
lean_dec_ref(v_type_1967_);
lean_dec(v_levelParams_1966_);
lean_dec(v_ctors_1965_);
lean_dec(v_numIndices_1964_);
lean_dec(v_numParams_1963_);
lean_del_object(v___x_1960_);
lean_dec_ref(v_val_1958_);
lean_dec(v___x_1949_);
lean_dec(v_indName_1937_);
v___x_1984_ = lean_box(0);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1984_);
v___x_1986_ = v___x_1978_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___f_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
lean_del_object(v___x_1978_);
v___x_1988_ = lean_box(0);
lean_inc(v_levelParams_1966_);
v___x_1989_ = l_List_mapTR_loop___at___00mkCtorIdx_spec__3(v_levelParams_1966_, v___x_1988_);
v___x_1990_ = lean_box(v___x_1938_);
v___x_1991_ = lean_box(v___x_1946_);
lean_inc(v_numParams_1963_);
v___f_1992_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_1992_, 0, v_numParams_1963_);
lean_closure_set(v___f_1992_, 1, v_indName_1937_);
lean_closure_set(v___f_1992_, 2, v___x_1989_);
lean_closure_set(v___f_1992_, 3, v___x_1988_);
lean_closure_set(v___f_1992_, 4, v___x_1990_);
lean_closure_set(v___f_1992_, 5, v___x_1991_);
lean_closure_set(v___f_1992_, 6, v_val_1958_);
lean_closure_set(v___f_1992_, 7, v___x_1974_);
lean_closure_set(v___f_1992_, 8, v_ctors_1965_);
lean_closure_set(v___f_1992_, 9, v___x_1949_);
lean_closure_set(v___f_1992_, 10, v_levelParams_1966_);
v___x_1993_ = lean_nat_add(v_numParams_1963_, v_numIndices_1964_);
lean_dec(v_numIndices_1964_);
lean_dec(v_numParams_1963_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set_tag(v___x_1960_, 1);
lean_ctor_set(v___x_1960_, 0, v___x_1993_);
v___x_1995_ = v___x_1960_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; 
v___x_1996_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_1967_, v___x_1995_, v___f_1992_, v___x_1938_, v___x_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_1996_;
}
}
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec(v___x_1974_);
lean_dec_ref(v_type_1967_);
lean_dec(v_levelParams_1966_);
lean_dec(v_ctors_1965_);
lean_dec(v_numIndices_1964_);
lean_dec(v_numParams_1963_);
lean_del_object(v___x_1960_);
lean_dec_ref(v_val_1958_);
lean_dec(v___x_1949_);
lean_dec(v_indName_1937_);
v_a_1999_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1975_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1975_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2009_; 
lean_dec_ref(v_type_1967_);
lean_dec(v_levelParams_1966_);
lean_dec(v_ctors_1965_);
lean_dec(v_numIndices_1964_);
lean_dec(v_numParams_1963_);
lean_del_object(v___x_1960_);
lean_dec_ref(v_val_1958_);
lean_dec(v___x_1949_);
lean_dec(v_indName_1937_);
v___x_2007_ = lean_box(0);
if (v_isShared_1972_ == 0)
{
lean_ctor_set(v___x_1971_, 0, v___x_2007_);
v___x_2009_ = v___x_1971_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec_ref(v_type_1967_);
lean_dec(v_levelParams_1966_);
lean_dec(v_ctors_1965_);
lean_dec(v_numIndices_1964_);
lean_dec(v_numParams_1963_);
lean_del_object(v___x_1960_);
lean_dec_ref(v_val_1958_);
lean_dec(v___x_1949_);
lean_dec(v_indName_1937_);
v_a_2012_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1968_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1968_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v_a_1957_);
lean_dec(v___x_1949_);
lean_dec(v_indName_1937_);
v___x_2021_ = lean_obj_once(&l_mkCtorIdx___lam__3___closed__2, &l_mkCtorIdx___lam__3___closed__2_once, _init_l_mkCtorIdx___lam__3___closed__2);
v___x_2022_ = l_panic___at___00mkCtorIdx_spec__13(v___x_2021_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
return v___x_2022_;
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
lean_dec(v___x_1949_);
lean_dec(v_indName_1937_);
v_a_2023_ = lean_ctor_get(v___x_1956_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_1956_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_1956_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2033_; 
lean_dec(v___x_1949_);
lean_dec(v_indName_1937_);
v___x_2031_ = lean_box(0);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 0, v___x_2031_);
v___x_2033_ = v___x_1953_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2036_, lean_object* v___x_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
uint8_t v___x_36862__boxed_2043_; lean_object* v_res_2044_; 
v___x_36862__boxed_2043_ = lean_unbox(v___x_2037_);
v_res_2044_ = l_mkCtorIdx___lam__3(v_indName_2036_, v___x_36862__boxed_2043_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_);
lean_dec(v___y_2041_);
lean_dec_ref(v___y_2040_);
lean_dec(v___y_2039_);
lean_dec_ref(v___y_2038_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__4(lean_object* v___x_2045_, lean_object* v_e_2046_){
_start:
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = l_Lean_indentD(v_e_2046_);
v___x_2048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2045_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5(lean_object* v___f_2049_, lean_object* v___f_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; 
v___x_2056_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2049_, v___f_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
v_a_2065_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2056_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2056_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5___boxed(lean_object* v___f_2073_, lean_object* v___f_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_mkCtorIdx___lam__5(v___f_2073_, v___f_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
return v_res_2080_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2082_ = ((lean_object*)(l_mkCtorIdx___closed__0));
v___x_2083_ = l_Lean_stringToMessageData(v___x_2082_);
return v___x_2083_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = ((lean_object*)(l_mkCtorIdx___closed__2));
v___x_2086_ = l_Lean_stringToMessageData(v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx(lean_object* v_indName_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___f_2101_; lean_object* v___f_2102_; uint8_t v___x_2103_; 
v___x_2093_ = lean_obj_once(&l_mkCtorIdx___closed__1, &l_mkCtorIdx___closed__1_once, _init_l_mkCtorIdx___closed__1);
v___x_2094_ = 0;
v___x_2095_ = lean_box(v___x_2094_);
lean_inc_n(v_indName_2087_, 2);
v___f_2096_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2096_, 0, v_indName_2087_);
lean_closure_set(v___f_2096_, 1, v___x_2095_);
v___x_2097_ = l_Lean_MessageData_ofConstName(v_indName_2087_, v___x_2094_);
v___x_2098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2093_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_obj_once(&l_mkCtorIdx___closed__3, &l_mkCtorIdx___closed__3_once, _init_l_mkCtorIdx___closed__3);
v___x_2100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2098_);
lean_ctor_set(v___x_2100_, 1, v___x_2099_);
v___f_2101_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2101_, 0, v___x_2100_);
v___f_2102_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2102_, 0, v___f_2096_);
lean_closure_set(v___f_2102_, 1, v___f_2101_);
v___x_2103_ = l_Lean_isPrivateName(v_indName_2087_);
lean_dec(v_indName_2087_);
if (v___x_2103_ == 0)
{
uint8_t v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = 1;
v___x_2105_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2102_, v___x_2104_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2102_, v___x_2094_, v_a_2088_, v_a_2089_, v_a_2090_, v_a_2091_);
return v___x_2106_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___boxed(lean_object* v_indName_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_mkCtorIdx(v_indName_2107_, v_a_2108_, v_a_2109_, v_a_2110_, v_a_2111_);
lean_dec(v_a_2111_);
lean_dec_ref(v_a_2110_);
lean_dec(v_a_2109_);
lean_dec_ref(v_a_2108_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(uint8_t v___x_2114_, lean_object* v___x_2115_, lean_object* v_as_2116_, lean_object* v_as_x27_2117_, lean_object* v_b_2118_, lean_object* v_a_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_2114_, v___x_2115_, v_as_x27_2117_, v_b_2118_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(lean_object* v___x_2126_, lean_object* v___x_2127_, lean_object* v_as_2128_, lean_object* v_as_x27_2129_, lean_object* v_b_2130_, lean_object* v_a_2131_, lean_object* v___y_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
uint8_t v___x_37169__boxed_2137_; lean_object* v_res_2138_; 
v___x_37169__boxed_2137_ = lean_unbox(v___x_2126_);
v_res_2138_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(v___x_37169__boxed_2137_, v___x_2127_, v_as_2128_, v_as_x27_2129_, v_b_2130_, v_a_2131_, v___y_2132_, v___y_2133_, v___y_2134_, v___y_2135_);
lean_dec(v___y_2135_);
lean_dec_ref(v___y_2134_);
lean_dec(v___y_2133_);
lean_dec_ref(v___y_2132_);
lean_dec(v_as_2128_);
lean_dec_ref(v___x_2127_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2139_, lean_object* v_name_2140_, uint8_t v_bi_2141_, lean_object* v_type_2142_, lean_object* v_k_2143_, uint8_t v_kind_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; 
v___x_2150_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_2140_, v_bi_2141_, v_type_2142_, v_k_2143_, v_kind_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
return v___x_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2151_, lean_object* v_name_2152_, lean_object* v_bi_2153_, lean_object* v_type_2154_, lean_object* v_k_2155_, lean_object* v_kind_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
uint8_t v_bi_boxed_2162_; uint8_t v_kind_boxed_2163_; lean_object* v_res_2164_; 
v_bi_boxed_2162_ = lean_unbox(v_bi_2153_);
v_kind_boxed_2163_ = lean_unbox(v_kind_2156_);
v_res_2164_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(v_00_u03b1_2151_, v_name_2152_, v_bi_boxed_2162_, v_type_2154_, v_k_2155_, v_kind_boxed_2163_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(lean_object* v_00_u03b1_2165_, lean_object* v_name_2166_, lean_object* v_type_2167_, lean_object* v_k_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_2166_, v_type_2167_, v_k_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2175_, lean_object* v_name_2176_, lean_object* v_type_2177_, lean_object* v_k_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(v_00_u03b1_2175_, v_name_2176_, v_type_2177_, v_k_2178_, v___y_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
lean_dec_ref(v___y_2179_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(lean_object* v_declName_2185_, uint8_t v_s_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_2185_, v_s_2186_, v___y_2188_, v___y_2190_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_declName_2193_, lean_object* v_s_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v_s_boxed_2200_; lean_object* v_res_2201_; 
v_s_boxed_2200_ = lean_unbox(v_s_2194_);
v_res_2201_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(v_declName_2193_, v_s_boxed_2200_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
lean_dec(v___y_2198_);
lean_dec_ref(v___y_2197_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(lean_object* v_env_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_2202_, v___y_2204_, v___y_2206_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(lean_object* v_env_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(v_env_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(lean_object* v_00_u03b1_2216_, lean_object* v_bs_2217_, lean_object* v_k_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_2217_, v_k_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(lean_object* v_00_u03b1_2225_, lean_object* v_bs_2226_, lean_object* v_k_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(v_00_u03b1_2225_, v_bs_2226_, v_k_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec(v___y_2229_);
lean_dec_ref(v___y_2228_);
lean_dec_ref(v_bs_2226_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(lean_object* v_00_u03b1_2234_, lean_object* v_bs_2235_, lean_object* v_k_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; 
v___x_2242_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_2235_, v_k_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_2243_, lean_object* v_bs_2244_, lean_object* v_k_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v_res_2251_; 
v_res_2251_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(v_00_u03b1_2243_, v_bs_2244_, v_k_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
return v_res_2251_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2252_, lean_object* v_constName_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v___x_2259_; 
v___x_2259_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2260_, lean_object* v_constName_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(v_00_u03b1_2260_, v_constName_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2268_, lean_object* v_msg_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2276_, lean_object* v_msg_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(v_00_u03b1_2276_, v_msg_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2284_, lean_object* v_ref_2285_, lean_object* v_constName_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2285_, v_constName_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2293_, lean_object* v_ref_2294_, lean_object* v_constName_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2293_, v_ref_2294_, v_constName_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v_ref_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object* v_00_u03b1_2302_, lean_object* v_ref_2303_, lean_object* v_msg_2304_, lean_object* v_declHint_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_){
_start:
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_2303_, v_msg_2304_, v_declHint_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object* v_00_u03b1_2312_, lean_object* v_ref_2313_, lean_object* v_msg_2314_, lean_object* v_declHint_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v_res_2321_; 
v_res_2321_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_2312_, v_ref_2313_, v_msg_2314_, v_declHint_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v_ref_2313_);
return v_res_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object* v_msg_2322_, lean_object* v_declHint_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_2322_, v_declHint_2323_, v___y_2327_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object* v_msg_2330_, lean_object* v_declHint_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_2330_, v_declHint_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
lean_dec(v___y_2335_);
lean_dec_ref(v___y_2334_);
lean_dec(v___y_2333_);
lean_dec_ref(v___y_2332_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object* v_00_u03b1_2338_, lean_object* v_ref_2339_, lean_object* v_msg_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_2339_, v_msg_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2347_, lean_object* v_ref_2348_, lean_object* v_msg_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_2347_, v_ref_2348_, v_msg_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v_ref_2348_);
return v_res_2355_;
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
