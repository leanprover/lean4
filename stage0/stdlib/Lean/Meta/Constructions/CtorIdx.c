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
static const lean_ctor_object l_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = ((lean_object*)(l_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_45_ = ((lean_object*)(l_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_46_ = l_Lean_Option_register___at___00initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_44_, v___x_45_, v___x_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_mkToCtorIdxName(lean_object* v_indName_50_){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_mkToCtorIdxName___closed__0));
v___x_52_ = l_Lean_Name_str___override(v_indName_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdxName(lean_object* v_indName_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = ((lean_object*)(l_mkCtorIdxName___closed__0));
v___x_56_ = l_Lean_Name_str___override(v_indName_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdxCore_x3f(lean_object* v_env_57_, lean_object* v_declName_58_){
_start:
{
if (lean_obj_tag(v_declName_58_) == 1)
{
lean_object* v_pre_59_; lean_object* v_str_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_pre_59_ = lean_ctor_get(v_declName_58_, 0);
lean_inc(v_pre_59_);
v_str_60_ = lean_ctor_get(v_declName_58_, 1);
lean_inc_ref(v_str_60_);
lean_dec_ref(v_declName_58_);
v___x_61_ = ((lean_object*)(l_mkCtorIdxName___closed__0));
v___x_62_ = lean_string_dec_eq(v_str_60_, v___x_61_);
lean_dec_ref(v_str_60_);
if (v___x_62_ == 0)
{
lean_object* v___x_63_; 
lean_dec(v_pre_59_);
lean_dec_ref(v_env_57_);
v___x_63_ = lean_box(0);
return v___x_63_;
}
else
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_isInductiveCore_x3f(v_env_57_, v_pre_59_);
return v___x_64_;
}
}
else
{
lean_object* v___x_65_; 
lean_dec(v_declName_58_);
lean_dec_ref(v_env_57_);
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg(lean_object* v_declName_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; lean_object* v_env_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = lean_st_ref_get(v_a_67_);
v_env_70_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref(v_env_70_);
lean_dec(v___x_69_);
v___x_71_ = l_isCtorIdxCore_x3f(v_env_70_, v_declName_66_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_isCtorIdx_x3f___redArg(v_declName_73_, v_a_74_);
lean_dec(v_a_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f(lean_object* v_declName_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_isCtorIdx_x3f___redArg(v_declName_77_, v_a_81_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_isCtorIdx_x3f___boxed(lean_object* v_declName_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_isCtorIdx_x3f(v_declName_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_90_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00mkCtorIdx_spec__0(lean_object* v_opts_91_, lean_object* v_opt_92_){
_start:
{
lean_object* v_name_93_; lean_object* v_defValue_94_; lean_object* v_map_95_; lean_object* v___x_96_; 
v_name_93_ = lean_ctor_get(v_opt_92_, 0);
v_defValue_94_ = lean_ctor_get(v_opt_92_, 1);
v_map_95_ = lean_ctor_get(v_opts_91_, 0);
v___x_96_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_95_, v_name_93_);
if (lean_obj_tag(v___x_96_) == 0)
{
uint8_t v___x_97_; 
v___x_97_ = lean_unbox(v_defValue_94_);
return v___x_97_;
}
else
{
lean_object* v_val_98_; 
v_val_98_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_val_98_);
lean_dec_ref(v___x_96_);
if (lean_obj_tag(v_val_98_) == 1)
{
uint8_t v_v_99_; 
v_v_99_ = lean_ctor_get_uint8(v_val_98_, 0);
lean_dec_ref(v_val_98_);
return v_v_99_;
}
else
{
uint8_t v___x_100_; 
lean_dec(v_val_98_);
v___x_100_ = lean_unbox(v_defValue_94_);
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00mkCtorIdx_spec__0___boxed(lean_object* v_opts_101_, lean_object* v_opt_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_opts_101_, v_opt_102_);
lean_dec_ref(v_opt_102_);
lean_dec_ref(v_opts_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(lean_object* v_constName_105_, uint8_t v_skipRealize_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v_env_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_109_ = lean_st_ref_get(v___y_107_);
v_env_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_env_110_);
lean_dec(v___x_109_);
v___x_111_ = l_Lean_Environment_contains(v_env_110_, v_constName_105_, v_skipRealize_106_);
v___x_112_ = lean_box(v___x_111_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_114_, lean_object* v_skipRealize_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
uint8_t v_skipRealize_boxed_118_; lean_object* v_res_119_; 
v_skipRealize_boxed_118_ = lean_unbox(v_skipRealize_115_);
v_res_119_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v_constName_114_, v_skipRealize_boxed_118_, v___y_116_);
lean_dec(v___y_116_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1(lean_object* v_constName_120_, uint8_t v_skipRealize_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v_constName_120_, v_skipRealize_121_, v___y_125_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00mkCtorIdx_spec__1___boxed(lean_object* v_constName_128_, lean_object* v_skipRealize_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
uint8_t v_skipRealize_boxed_135_; lean_object* v_res_136_; 
v_skipRealize_boxed_135_ = lean_unbox(v_skipRealize_129_);
v_res_136_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1(v_constName_128_, v_skipRealize_boxed_135_, v___y_130_, v___y_131_, v___y_132_, v___y_133_);
lean_dec(v___y_133_);
lean_dec_ref(v___y_132_);
lean_dec(v___y_131_);
lean_dec_ref(v___y_130_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(lean_object* v_k_137_, lean_object* v_b_138_, lean_object* v_c_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_){
_start:
{
lean_object* v___x_145_; 
lean_inc(v___y_143_);
lean_inc_ref(v___y_142_);
lean_inc(v___y_141_);
lean_inc_ref(v___y_140_);
v___x_145_ = lean_apply_7(v_k_137_, v_b_138_, v_c_139_, v___y_140_, v___y_141_, v___y_142_, v___y_143_, lean_box(0));
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object* v_k_146_, lean_object* v_b_147_, lean_object* v_c_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0(v_k_146_, v_b_147_, v_c_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec(v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec_ref(v___y_149_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(lean_object* v_type_155_, lean_object* v_maxFVars_x3f_156_, lean_object* v_k_157_, uint8_t v_cleanupAnnotations_158_, uint8_t v_whnfType_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___f_165_; lean_object* v___x_166_; 
v___f_165_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_165_, 0, v_k_157_);
v___x_166_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_155_, v_maxFVars_x3f_156_, v___f_165_, v_cleanupAnnotations_158_, v_whnfType_159_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_174_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_174_ == 0)
{
v___x_169_ = v___x_166_;
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_a_167_);
lean_dec(v___x_166_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_174_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_172_; 
if (v_isShared_170_ == 0)
{
v___x_172_ = v___x_169_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v_a_167_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
v_a_175_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_166_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_166_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_183_, lean_object* v_maxFVars_x3f_184_, lean_object* v_k_185_, lean_object* v_cleanupAnnotations_186_, lean_object* v_whnfType_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_193_; uint8_t v_whnfType_boxed_194_; lean_object* v_res_195_; 
v_cleanupAnnotations_boxed_193_ = lean_unbox(v_cleanupAnnotations_186_);
v_whnfType_boxed_194_ = lean_unbox(v_whnfType_187_);
v_res_195_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_183_, v_maxFVars_x3f_184_, v_k_185_, v_cleanupAnnotations_boxed_193_, v_whnfType_boxed_194_, v___y_188_, v___y_189_, v___y_190_, v___y_191_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(lean_object* v_00_u03b1_196_, lean_object* v_type_197_, lean_object* v_maxFVars_x3f_198_, lean_object* v_k_199_, uint8_t v_cleanupAnnotations_200_, uint8_t v_whnfType_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_197_, v_maxFVars_x3f_198_, v_k_199_, v_cleanupAnnotations_200_, v_whnfType_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_208_, lean_object* v_type_209_, lean_object* v_maxFVars_x3f_210_, lean_object* v_k_211_, lean_object* v_cleanupAnnotations_212_, lean_object* v_whnfType_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_219_; uint8_t v_whnfType_boxed_220_; lean_object* v_res_221_; 
v_cleanupAnnotations_boxed_219_ = lean_unbox(v_cleanupAnnotations_212_);
v_whnfType_boxed_220_ = lean_unbox(v_whnfType_213_);
v_res_221_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5(v_00_u03b1_208_, v_type_209_, v_maxFVars_x3f_210_, v_k_211_, v_cleanupAnnotations_boxed_219_, v_whnfType_boxed_220_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(lean_object* v_name_222_, lean_object* v_levelParams_223_, lean_object* v_type_224_, lean_object* v_value_225_, lean_object* v_hints_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; uint8_t v___y_231_; uint8_t v___y_238_; lean_object* v_env_241_; uint8_t v___x_242_; 
v___x_229_ = lean_st_ref_get(v___y_227_);
v_env_241_ = lean_ctor_get(v___x_229_, 0);
lean_inc_ref_n(v_env_241_, 2);
lean_dec(v___x_229_);
v___x_242_ = l_Lean_Environment_hasUnsafe(v_env_241_, v_type_224_);
if (v___x_242_ == 0)
{
uint8_t v___x_243_; 
v___x_243_ = l_Lean_Environment_hasUnsafe(v_env_241_, v_value_225_);
v___y_238_ = v___x_243_;
goto v___jp_237_;
}
else
{
lean_dec_ref(v_env_241_);
v___y_238_ = v___x_242_;
goto v___jp_237_;
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
lean_inc(v_name_222_);
v___x_232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_232_, 0, v_name_222_);
lean_ctor_set(v___x_232_, 1, v_levelParams_223_);
lean_ctor_set(v___x_232_, 2, v_type_224_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_234_, 0, v_name_222_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_235_, 0, v___x_232_);
lean_ctor_set(v___x_235_, 1, v_value_225_);
lean_ctor_set(v___x_235_, 2, v_hints_226_);
lean_ctor_set(v___x_235_, 3, v___x_234_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*4, v___y_231_);
v___x_236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
return v___x_236_;
}
v___jp_237_:
{
if (v___y_238_ == 0)
{
uint8_t v___x_239_; 
v___x_239_ = 1;
v___y_231_ = v___x_239_;
goto v___jp_230_;
}
else
{
uint8_t v___x_240_; 
v___x_240_ = 0;
v___y_231_ = v___x_240_;
goto v___jp_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_244_, lean_object* v_levelParams_245_, lean_object* v_type_246_, lean_object* v_value_247_, lean_object* v_hints_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v_name_244_, v_levelParams_245_, v_type_246_, v_value_247_, v_hints_248_, v___y_249_);
lean_dec(v___y_249_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(lean_object* v_name_252_, lean_object* v_levelParams_253_, lean_object* v_type_254_, lean_object* v_value_255_, lean_object* v_hints_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v_name_252_, v_levelParams_253_, v_type_254_, v_value_255_, v_hints_256_, v___y_260_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___boxed(lean_object* v_name_263_, lean_object* v_levelParams_264_, lean_object* v_type_265_, lean_object* v_value_266_, lean_object* v_hints_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8(v_name_263_, v_levelParams_264_, v_type_265_, v_value_266_, v_hints_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13(lean_object* v_msg_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___f_281_; lean_object* v___x_26644__overap_282_; lean_object* v___x_283_; 
v___f_281_ = ((lean_object*)(l_panic___at___00mkCtorIdx_spec__13___closed__0));
v___x_26644__overap_282_ = lean_panic_fn_borrowed(v___f_281_, v_msg_275_);
lean_inc(v___y_279_);
lean_inc_ref(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
v___x_283_ = lean_apply_5(v___x_26644__overap_282_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, lean_box(0));
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00mkCtorIdx_spec__13___boxed(lean_object* v_msg_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_panic___at___00mkCtorIdx_spec__13(v_msg_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(lean_object* v___y_291_, uint8_t v_isExporting_292_, lean_object* v___x_293_, lean_object* v___y_294_, lean_object* v___x_295_, lean_object* v_a_x3f_296_){
_start:
{
lean_object* v___x_298_; lean_object* v_env_299_; lean_object* v_nextMacroScope_300_; lean_object* v_ngen_301_; lean_object* v_auxDeclNGen_302_; lean_object* v_traceState_303_; lean_object* v_messages_304_; lean_object* v_infoState_305_; lean_object* v_snapshotTasks_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_331_; 
v___x_298_ = lean_st_ref_take(v___y_291_);
v_env_299_ = lean_ctor_get(v___x_298_, 0);
v_nextMacroScope_300_ = lean_ctor_get(v___x_298_, 1);
v_ngen_301_ = lean_ctor_get(v___x_298_, 2);
v_auxDeclNGen_302_ = lean_ctor_get(v___x_298_, 3);
v_traceState_303_ = lean_ctor_get(v___x_298_, 4);
v_messages_304_ = lean_ctor_get(v___x_298_, 6);
v_infoState_305_ = lean_ctor_get(v___x_298_, 7);
v_snapshotTasks_306_ = lean_ctor_get(v___x_298_, 8);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_331_ == 0)
{
lean_object* v_unused_332_; 
v_unused_332_ = lean_ctor_get(v___x_298_, 5);
lean_dec(v_unused_332_);
v___x_308_ = v___x_298_;
v_isShared_309_ = v_isSharedCheck_331_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_snapshotTasks_306_);
lean_inc(v_infoState_305_);
lean_inc(v_messages_304_);
lean_inc(v_traceState_303_);
lean_inc(v_auxDeclNGen_302_);
lean_inc(v_ngen_301_);
lean_inc(v_nextMacroScope_300_);
lean_inc(v_env_299_);
lean_dec(v___x_298_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_331_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_312_; 
v___x_310_ = l_Lean_Environment_setExporting(v_env_299_, v_isExporting_292_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 5, v___x_293_);
lean_ctor_set(v___x_308_, 0, v___x_310_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_310_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_nextMacroScope_300_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_ngen_301_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v_auxDeclNGen_302_);
lean_ctor_set(v_reuseFailAlloc_330_, 4, v_traceState_303_);
lean_ctor_set(v_reuseFailAlloc_330_, 5, v___x_293_);
lean_ctor_set(v_reuseFailAlloc_330_, 6, v_messages_304_);
lean_ctor_set(v_reuseFailAlloc_330_, 7, v_infoState_305_);
lean_ctor_set(v_reuseFailAlloc_330_, 8, v_snapshotTasks_306_);
v___x_312_ = v_reuseFailAlloc_330_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v_mctx_315_; lean_object* v_zetaDeltaFVarIds_316_; lean_object* v_postponed_317_; lean_object* v_diag_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_328_; 
v___x_313_ = lean_st_ref_set(v___y_291_, v___x_312_);
v___x_314_ = lean_st_ref_take(v___y_294_);
v_mctx_315_ = lean_ctor_get(v___x_314_, 0);
v_zetaDeltaFVarIds_316_ = lean_ctor_get(v___x_314_, 2);
v_postponed_317_ = lean_ctor_get(v___x_314_, 3);
v_diag_318_ = lean_ctor_get(v___x_314_, 4);
v_isSharedCheck_328_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v___x_314_, 1);
lean_dec(v_unused_329_);
v___x_320_ = v___x_314_;
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_diag_318_);
lean_inc(v_postponed_317_);
lean_inc(v_zetaDeltaFVarIds_316_);
lean_inc(v_mctx_315_);
lean_dec(v___x_314_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_328_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 1, v___x_295_);
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_mctx_315_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_zetaDeltaFVarIds_316_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_postponed_317_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v_diag_318_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_st_ref_set(v___y_294_, v___x_323_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object* v___y_333_, lean_object* v_isExporting_334_, lean_object* v___x_335_, lean_object* v___y_336_, lean_object* v___x_337_, lean_object* v_a_x3f_338_, lean_object* v___y_339_){
_start:
{
uint8_t v_isExporting_boxed_340_; lean_object* v_res_341_; 
v_isExporting_boxed_340_ = lean_unbox(v_isExporting_334_);
v_res_341_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_333_, v_isExporting_boxed_340_, v___x_335_, v___y_336_, v___x_337_, v_a_x3f_338_);
lean_dec(v_a_x3f_338_);
lean_dec(v___y_336_);
lean_dec(v___y_333_);
return v_res_341_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_342_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__0);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_347_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__1);
v___x_348_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_ctor_set(v___x_348_, 2, v___x_347_);
lean_ctor_set(v___x_348_, 3, v___x_347_);
lean_ctor_set(v___x_348_, 4, v___x_347_);
lean_ctor_set(v___x_348_, 5, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(lean_object* v_x_349_, uint8_t v_isExporting_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_){
_start:
{
lean_object* v___x_356_; lean_object* v_env_357_; uint8_t v_isExporting_358_; lean_object* v___x_359_; lean_object* v_env_360_; lean_object* v_nextMacroScope_361_; lean_object* v_ngen_362_; lean_object* v_auxDeclNGen_363_; lean_object* v_traceState_364_; lean_object* v_messages_365_; lean_object* v_infoState_366_; lean_object* v_snapshotTasks_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_421_; 
v___x_356_ = lean_st_ref_get(v___y_354_);
v_env_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc_ref(v_env_357_);
lean_dec(v___x_356_);
v_isExporting_358_ = lean_ctor_get_uint8(v_env_357_, sizeof(void*)*8);
lean_dec_ref(v_env_357_);
v___x_359_ = lean_st_ref_take(v___y_354_);
v_env_360_ = lean_ctor_get(v___x_359_, 0);
v_nextMacroScope_361_ = lean_ctor_get(v___x_359_, 1);
v_ngen_362_ = lean_ctor_get(v___x_359_, 2);
v_auxDeclNGen_363_ = lean_ctor_get(v___x_359_, 3);
v_traceState_364_ = lean_ctor_get(v___x_359_, 4);
v_messages_365_ = lean_ctor_get(v___x_359_, 6);
v_infoState_366_ = lean_ctor_get(v___x_359_, 7);
v_snapshotTasks_367_ = lean_ctor_get(v___x_359_, 8);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_421_ == 0)
{
lean_object* v_unused_422_; 
v_unused_422_ = lean_ctor_get(v___x_359_, 5);
lean_dec(v_unused_422_);
v___x_369_ = v___x_359_;
v_isShared_370_ = v_isSharedCheck_421_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_snapshotTasks_367_);
lean_inc(v_infoState_366_);
lean_inc(v_messages_365_);
lean_inc(v_traceState_364_);
lean_inc(v_auxDeclNGen_363_);
lean_inc(v_ngen_362_);
lean_inc(v_nextMacroScope_361_);
lean_inc(v_env_360_);
lean_dec(v___x_359_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_421_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_371_ = l_Lean_Environment_setExporting(v_env_360_, v_isExporting_350_);
v___x_372_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 5, v___x_372_);
lean_ctor_set(v___x_369_, 0, v___x_371_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_nextMacroScope_361_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v_ngen_362_);
lean_ctor_set(v_reuseFailAlloc_420_, 3, v_auxDeclNGen_363_);
lean_ctor_set(v_reuseFailAlloc_420_, 4, v_traceState_364_);
lean_ctor_set(v_reuseFailAlloc_420_, 5, v___x_372_);
lean_ctor_set(v_reuseFailAlloc_420_, 6, v_messages_365_);
lean_ctor_set(v_reuseFailAlloc_420_, 7, v_infoState_366_);
lean_ctor_set(v_reuseFailAlloc_420_, 8, v_snapshotTasks_367_);
v___x_374_ = v_reuseFailAlloc_420_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v_mctx_377_; lean_object* v_zetaDeltaFVarIds_378_; lean_object* v_postponed_379_; lean_object* v_diag_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_418_; 
v___x_375_ = lean_st_ref_set(v___y_354_, v___x_374_);
v___x_376_ = lean_st_ref_take(v___y_352_);
v_mctx_377_ = lean_ctor_get(v___x_376_, 0);
v_zetaDeltaFVarIds_378_ = lean_ctor_get(v___x_376_, 2);
v_postponed_379_ = lean_ctor_get(v___x_376_, 3);
v_diag_380_ = lean_ctor_get(v___x_376_, 4);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; 
v_unused_419_ = lean_ctor_get(v___x_376_, 1);
lean_dec(v_unused_419_);
v___x_382_ = v___x_376_;
v_isShared_383_ = v_isSharedCheck_418_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_diag_380_);
lean_inc(v_postponed_379_);
lean_inc(v_zetaDeltaFVarIds_378_);
lean_inc(v_mctx_377_);
lean_dec(v___x_376_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_418_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v___x_386_; 
v___x_384_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v___x_384_);
v___x_386_ = v___x_382_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_mctx_377_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v___x_384_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_zetaDeltaFVarIds_378_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_postponed_379_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_diag_380_);
v___x_386_ = v_reuseFailAlloc_417_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v_r_388_; 
v___x_387_ = lean_st_ref_set(v___y_352_, v___x_386_);
lean_inc(v___y_354_);
lean_inc_ref(v___y_353_);
lean_inc(v___y_352_);
lean_inc_ref(v___y_351_);
v_r_388_ = lean_apply_5(v_x_349_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, lean_box(0));
if (lean_obj_tag(v_r_388_) == 0)
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_405_; 
v_a_389_ = lean_ctor_get(v_r_388_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v_r_388_);
if (v_isSharedCheck_405_ == 0)
{
v___x_391_ = v_r_388_;
v_isShared_392_ = v_isSharedCheck_405_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v_r_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_405_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
lean_inc(v_a_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 1);
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_404_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v___x_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
v___x_395_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_354_, v_isExporting_358_, v___x_372_, v___y_352_, v___x_384_, v___x_394_);
lean_dec_ref(v___x_394_);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_402_ == 0)
{
lean_object* v_unused_403_; 
v_unused_403_ = lean_ctor_get(v___x_395_, 0);
lean_dec(v_unused_403_);
v___x_397_ = v___x_395_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_dec(v___x_395_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v_a_389_);
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_389_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
else
{
lean_object* v_a_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
v_a_406_ = lean_ctor_get(v_r_388_, 0);
lean_inc(v_a_406_);
lean_dec_ref(v_r_388_);
v___x_407_ = lean_box(0);
v___x_408_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___lam__0(v___y_354_, v_isExporting_358_, v___x_372_, v___y_352_, v___x_384_, v___x_407_);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v___x_408_, 0);
lean_dec(v_unused_416_);
v___x_410_ = v___x_408_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_dec(v___x_408_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set_tag(v___x_410_, 1);
lean_ctor_set(v___x_410_, 0, v_a_406_);
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_406_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___boxed(lean_object* v_x_423_, lean_object* v_isExporting_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_){
_start:
{
uint8_t v_isExporting_boxed_430_; lean_object* v_res_431_; 
v_isExporting_boxed_430_ = lean_unbox(v_isExporting_424_);
v_res_431_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v_x_423_, v_isExporting_boxed_430_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
lean_dec(v___y_428_);
lean_dec_ref(v___y_427_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14(lean_object* v_00_u03b1_432_, lean_object* v_x_433_, uint8_t v_isExporting_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v_x_433_, v_isExporting_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00mkCtorIdx_spec__14___boxed(lean_object* v_00_u03b1_441_, lean_object* v_x_442_, lean_object* v_isExporting_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
uint8_t v_isExporting_boxed_449_; lean_object* v_res_450_; 
v_isExporting_boxed_449_ = lean_unbox(v_isExporting_443_);
v_res_450_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14(v_00_u03b1_441_, v_x_442_, v_isExporting_boxed_449_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
lean_object* v___x_457_; lean_object* v_env_458_; lean_object* v___x_459_; lean_object* v_mctx_460_; lean_object* v_lctx_461_; lean_object* v_options_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_457_ = lean_st_ref_get(v___y_455_);
v_env_458_ = lean_ctor_get(v___x_457_, 0);
lean_inc_ref(v_env_458_);
lean_dec(v___x_457_);
v___x_459_ = lean_st_ref_get(v___y_453_);
v_mctx_460_ = lean_ctor_get(v___x_459_, 0);
lean_inc_ref(v_mctx_460_);
lean_dec(v___x_459_);
v_lctx_461_ = lean_ctor_get(v___y_452_, 2);
v_options_462_ = lean_ctor_get(v___y_454_, 2);
lean_inc_ref(v_options_462_);
lean_inc_ref(v_lctx_461_);
v___x_463_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_463_, 0, v_env_458_);
lean_ctor_set(v___x_463_, 1, v_mctx_460_);
lean_ctor_set(v___x_463_, 2, v_lctx_461_);
lean_ctor_set(v___x_463_, 3, v_options_462_);
v___x_464_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_msgData_451_);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_ref_479_; lean_object* v___x_480_; lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_489_; 
v_ref_479_ = lean_ctor_get(v___y_476_, 5);
v___x_480_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5_spec__11(v_msg_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
v_a_481_ = lean_ctor_get(v___x_480_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_489_ == 0)
{
v___x_483_ = v___x_480_;
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_489_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_487_; 
lean_inc(v_ref_479_);
v___x_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_485_, 0, v_ref_479_);
lean_ctor_set(v___x_485_, 1, v_a_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 1);
lean_ctor_set(v___x_483_, 0, v___x_485_);
v___x_487_ = v___x_483_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_496_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_instMonadEIO(lean_box(0));
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(lean_object* v_msg_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v_toApplicative_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_571_; 
v___x_508_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__0);
v___x_509_ = l_StateRefT_x27_instMonad___redArg(v___x_508_);
v_toApplicative_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_571_ == 0)
{
lean_object* v_unused_572_; 
v_unused_572_ = lean_ctor_get(v___x_509_, 1);
lean_dec(v_unused_572_);
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_571_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_toApplicative_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_571_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_toFunctor_514_; lean_object* v_toSeq_515_; lean_object* v_toSeqLeft_516_; lean_object* v_toSeqRight_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_569_; 
v_toFunctor_514_ = lean_ctor_get(v_toApplicative_510_, 0);
v_toSeq_515_ = lean_ctor_get(v_toApplicative_510_, 2);
v_toSeqLeft_516_ = lean_ctor_get(v_toApplicative_510_, 3);
v_toSeqRight_517_ = lean_ctor_get(v_toApplicative_510_, 4);
v_isSharedCheck_569_ = !lean_is_exclusive(v_toApplicative_510_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; 
v_unused_570_ = lean_ctor_get(v_toApplicative_510_, 1);
lean_dec(v_unused_570_);
v___x_519_ = v_toApplicative_510_;
v_isShared_520_ = v_isSharedCheck_569_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_toSeqRight_517_);
lean_inc(v_toSeqLeft_516_);
lean_inc(v_toSeq_515_);
lean_inc(v_toFunctor_514_);
lean_dec(v_toApplicative_510_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_569_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___f_521_; lean_object* v___f_522_; lean_object* v___f_523_; lean_object* v___f_524_; lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___f_527_; lean_object* v___f_528_; lean_object* v___x_530_; 
v___f_521_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__1));
v___f_522_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_514_);
v___f_523_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_523_, 0, v_toFunctor_514_);
v___f_524_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_524_, 0, v_toFunctor_514_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v___f_523_);
lean_ctor_set(v___x_525_, 1, v___f_524_);
v___f_526_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_526_, 0, v_toSeqRight_517_);
v___f_527_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_527_, 0, v_toSeqLeft_516_);
v___f_528_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_528_, 0, v_toSeq_515_);
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 4, v___f_526_);
lean_ctor_set(v___x_519_, 3, v___f_527_);
lean_ctor_set(v___x_519_, 2, v___f_528_);
lean_ctor_set(v___x_519_, 1, v___f_521_);
lean_ctor_set(v___x_519_, 0, v___x_525_);
v___x_530_ = v___x_519_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___f_521_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v___f_528_);
lean_ctor_set(v_reuseFailAlloc_568_, 3, v___f_527_);
lean_ctor_set(v_reuseFailAlloc_568_, 4, v___f_526_);
v___x_530_ = v_reuseFailAlloc_568_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
lean_object* v___x_532_; 
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___f_522_);
lean_ctor_set(v___x_512_, 0, v___x_530_);
v___x_532_ = v___x_512_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___f_522_);
v___x_532_ = v_reuseFailAlloc_567_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v_toApplicative_534_; lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_565_; 
v___x_533_ = l_StateRefT_x27_instMonad___redArg(v___x_532_);
v_toApplicative_534_ = lean_ctor_get(v___x_533_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v___x_533_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v___x_533_, 1);
lean_dec(v_unused_566_);
v___x_536_ = v___x_533_;
v_isShared_537_ = v_isSharedCheck_565_;
goto v_resetjp_535_;
}
else
{
lean_inc(v_toApplicative_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_565_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v_toFunctor_538_; lean_object* v_toSeq_539_; lean_object* v_toSeqLeft_540_; lean_object* v_toSeqRight_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_563_; 
v_toFunctor_538_ = lean_ctor_get(v_toApplicative_534_, 0);
v_toSeq_539_ = lean_ctor_get(v_toApplicative_534_, 2);
v_toSeqLeft_540_ = lean_ctor_get(v_toApplicative_534_, 3);
v_toSeqRight_541_ = lean_ctor_get(v_toApplicative_534_, 4);
v_isSharedCheck_563_ = !lean_is_exclusive(v_toApplicative_534_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; 
v_unused_564_ = lean_ctor_get(v_toApplicative_534_, 1);
lean_dec(v_unused_564_);
v___x_543_ = v_toApplicative_534_;
v_isShared_544_ = v_isSharedCheck_563_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_toSeqRight_541_);
lean_inc(v_toSeqLeft_540_);
lean_inc(v_toSeq_539_);
lean_inc(v_toFunctor_538_);
lean_dec(v_toApplicative_534_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_563_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___f_545_; lean_object* v___f_546_; lean_object* v___f_547_; lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___f_552_; lean_object* v___x_554_; 
v___f_545_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__3));
v___f_546_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_538_);
v___f_547_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_547_, 0, v_toFunctor_538_);
v___f_548_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_548_, 0, v_toFunctor_538_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___f_547_);
lean_ctor_set(v___x_549_, 1, v___f_548_);
v___f_550_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_550_, 0, v_toSeqRight_541_);
v___f_551_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_551_, 0, v_toSeqLeft_540_);
v___f_552_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_552_, 0, v_toSeq_539_);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 4, v___f_550_);
lean_ctor_set(v___x_543_, 3, v___f_551_);
lean_ctor_set(v___x_543_, 2, v___f_552_);
lean_ctor_set(v___x_543_, 1, v___f_545_);
lean_ctor_set(v___x_543_, 0, v___x_549_);
v___x_554_ = v___x_543_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v___f_545_);
lean_ctor_set(v_reuseFailAlloc_562_, 2, v___f_552_);
lean_ctor_set(v_reuseFailAlloc_562_, 3, v___f_551_);
lean_ctor_set(v_reuseFailAlloc_562_, 4, v___f_550_);
v___x_554_ = v_reuseFailAlloc_562_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v___f_546_);
lean_ctor_set(v___x_536_, 0, v___x_554_);
v___x_556_ = v___x_536_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v___f_546_);
v___x_556_ = v_reuseFailAlloc_561_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_30006__overap_559_; lean_object* v___x_560_; 
v___x_557_ = lean_box(0);
v___x_558_ = l_instInhabitedOfMonad___redArg(v___x_556_, v___x_557_);
v___x_30006__overap_559_ = lean_panic_fn_borrowed(v___x_558_, v_msg_502_);
lean_dec(v___x_558_);
lean_inc(v___y_506_);
lean_inc_ref(v___y_505_);
lean_inc(v___y_504_);
lean_inc_ref(v___y_503_);
v___x_560_ = lean_apply_5(v___x_30006__overap_559_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, lean_box(0));
return v___x_560_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v_msg_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
return v_res_579_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__0));
v___x_582_ = l_Lean_stringToMessageData(v___x_581_);
return v___x_582_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__2));
v___x_585_ = l_Lean_stringToMessageData(v___x_584_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_589_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_590_ = lean_unsigned_to_nat(11u);
v___x_591_ = lean_unsigned_to_nat(122u);
v___x_592_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__5));
v___x_593_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__4));
v___x_594_ = l_mkPanicMessageWithDecl(v___x_593_, v___x_592_, v___x_591_, v___x_590_, v___x_589_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(lean_object* v_constName_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___x_609_; lean_object* v_env_610_; uint8_t v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_st_ref_get(v___y_599_);
v_env_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc_ref(v_env_610_);
lean_dec(v___x_609_);
v___x_611_ = 0;
lean_inc(v_constName_595_);
v___x_612_ = l_Lean_Environment_findAsync_x3f(v_env_610_, v_constName_595_, v___x_611_);
if (lean_obj_tag(v___x_612_) == 1)
{
lean_object* v_val_613_; uint8_t v_kind_614_; 
v_val_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_val_613_);
lean_dec_ref(v___x_612_);
v_kind_614_ = lean_ctor_get_uint8(v_val_613_, sizeof(void*)*3);
if (v_kind_614_ == 6)
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_613_);
if (lean_obj_tag(v___x_615_) == 6)
{
lean_object* v_val_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_623_; 
lean_dec(v_constName_595_);
v_val_616_ = lean_ctor_get(v___x_615_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_615_);
if (v_isSharedCheck_623_ == 0)
{
v___x_618_ = v___x_615_;
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_val_616_);
lean_dec(v___x_615_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_623_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v___x_621_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set_tag(v___x_618_, 0);
v___x_621_ = v___x_618_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_val_616_);
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
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec_ref(v___x_615_);
v___x_624_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__7);
v___x_625_ = l_panic___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__6(v___x_624_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_625_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_634_; 
v_a_626_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_634_ == 0)
{
v___x_628_ = v___x_625_;
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_625_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_634_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
if (lean_obj_tag(v_a_626_) == 0)
{
lean_del_object(v___x_628_);
goto v___jp_601_;
}
else
{
lean_object* v_val_630_; lean_object* v___x_632_; 
lean_dec(v_constName_595_);
v_val_630_ = lean_ctor_get(v_a_626_, 0);
lean_inc(v_val_630_);
lean_dec_ref(v_a_626_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v_val_630_);
v___x_632_ = v___x_628_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v_val_630_);
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
else
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_642_; 
lean_dec(v_constName_595_);
v_a_635_ = lean_ctor_get(v___x_625_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_625_);
if (v_isSharedCheck_642_ == 0)
{
v___x_637_ = v___x_625_;
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_625_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_642_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_640_; 
if (v_isShared_638_ == 0)
{
v___x_640_ = v___x_637_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
else
{
lean_dec(v_val_613_);
goto v___jp_601_;
}
}
else
{
lean_dec(v___x_612_);
goto v___jp_601_;
}
v___jp_601_:
{
lean_object* v___x_602_; uint8_t v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_602_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_603_ = 0;
v___x_604_ = l_Lean_MessageData_ofConstName(v_constName_595_, v___x_603_);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_602_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__3);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_607_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___boxed(lean_object* v_constName_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_constName_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_650_, uint8_t v___x_651_, uint8_t v___x_652_, uint8_t v___x_653_, lean_object* v_ys_654_, lean_object* v_x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_661_ = l_Lean_mkRawNatLit(v_cidx_650_);
v___x_662_ = l_Lean_Meta_mkLambdaFVars(v_ys_654_, v___x_661_, v___x_651_, v___x_652_, v___x_651_, v___x_652_, v___x_653_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v_ys_667_, lean_object* v_x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v___x_34830__boxed_674_; uint8_t v___x_34831__boxed_675_; uint8_t v___x_34832__boxed_676_; lean_object* v_res_677_; 
v___x_34830__boxed_674_ = lean_unbox(v___x_664_);
v___x_34831__boxed_675_ = lean_unbox(v___x_665_);
v___x_34832__boxed_676_ = lean_unbox(v___x_666_);
v_res_677_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0(v_cidx_663_, v___x_34830__boxed_674_, v___x_34831__boxed_675_, v___x_34832__boxed_676_, v_ys_667_, v_x_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec_ref(v_x_668_);
lean_dec_ref(v_ys_667_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(uint8_t v___x_678_, lean_object* v___x_679_, lean_object* v_as_x27_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
if (lean_obj_tag(v_as_x27_680_) == 0)
{
lean_object* v___x_687_; 
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v_b_681_);
return v___x_687_;
}
else
{
lean_object* v_head_688_; lean_object* v_tail_689_; lean_object* v___x_690_; 
v_head_688_ = lean_ctor_get(v_as_x27_680_, 0);
lean_inc(v_head_688_);
v_tail_689_ = lean_ctor_get(v_as_x27_680_, 1);
lean_inc(v_tail_689_);
lean_dec_ref(v_as_x27_680_);
v___x_690_ = l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4(v_head_688_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_690_) == 0)
{
lean_object* v_a_691_; lean_object* v_toConstantVal_692_; lean_object* v_cidx_693_; lean_object* v_numFields_694_; lean_object* v_type_695_; lean_object* v___x_696_; 
v_a_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_a_691_);
lean_dec_ref(v___x_690_);
v_toConstantVal_692_ = lean_ctor_get(v_a_691_, 0);
lean_inc_ref(v_toConstantVal_692_);
v_cidx_693_ = lean_ctor_get(v_a_691_, 2);
lean_inc(v_cidx_693_);
v_numFields_694_ = lean_ctor_get(v_a_691_, 4);
lean_inc(v_numFields_694_);
lean_dec(v_a_691_);
v_type_695_ = lean_ctor_get(v_toConstantVal_692_, 2);
lean_inc_ref(v_type_695_);
lean_dec_ref(v_toConstantVal_692_);
v___x_696_ = l_Lean_Meta_instantiateForall(v_type_695_, v___x_679_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_714_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_714_ == 0)
{
v___x_699_ = v___x_696_;
v_isShared_700_ = v_isSharedCheck_714_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_714_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
uint8_t v___x_701_; uint8_t v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___f_706_; lean_object* v___x_708_; 
v___x_701_ = 0;
v___x_702_ = 1;
v___x_703_ = lean_box(v___x_701_);
v___x_704_ = lean_box(v___x_678_);
v___x_705_ = lean_box(v___x_702_);
v___f_706_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_706_, 0, v_cidx_693_);
lean_closure_set(v___f_706_, 1, v___x_703_);
lean_closure_set(v___f_706_, 2, v___x_704_);
lean_closure_set(v___f_706_, 3, v___x_705_);
if (v_isShared_700_ == 0)
{
lean_ctor_set_tag(v___x_699_, 1);
lean_ctor_set(v___x_699_, 0, v_numFields_694_);
v___x_708_ = v___x_699_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_numFields_694_);
v___x_708_ = v_reuseFailAlloc_713_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_a_697_, v___x_708_, v___f_706_, v___x_701_, v___x_701_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref(v___x_709_);
v___x_711_ = l_Lean_Expr_app___override(v_b_681_, v_a_710_);
v_as_x27_680_ = v_tail_689_;
v_b_681_ = v___x_711_;
goto _start;
}
else
{
lean_dec(v_tail_689_);
lean_dec_ref(v_b_681_);
return v___x_709_;
}
}
}
}
else
{
lean_dec(v_numFields_694_);
lean_dec(v_cidx_693_);
lean_dec(v_tail_689_);
lean_dec_ref(v_b_681_);
return v___x_696_;
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v_tail_689_);
lean_dec_ref(v_b_681_);
v_a_715_ = lean_ctor_get(v___x_690_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_690_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_690_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_690_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_723_, lean_object* v___x_724_, lean_object* v_as_x27_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
uint8_t v___x_34861__boxed_732_; lean_object* v_res_733_; 
v___x_34861__boxed_732_ = lean_unbox(v___x_723_);
v_res_733_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_34861__boxed_732_, v___x_724_, v_as_x27_725_, v_b_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec_ref(v___x_724_);
return v_res_733_;
}
}
static lean_object* _init_l_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
v___x_735_ = l_Lean_Level_succ___override(v___x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0(lean_object* v_xs_736_, uint8_t v___x_737_, uint8_t v___x_738_, uint8_t v___x_739_, lean_object* v_val_740_, lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v___x_744_, lean_object* v___x_745_, lean_object* v_ctors_746_, lean_object* v___x_747_, lean_object* v_x_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_value_755_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = l_Lean_InductiveVal_numCtors(v_val_740_);
v___x_759_ = lean_unsigned_to_nat(1u);
v___x_760_ = lean_nat_dec_eq(v___x_758_, v___x_759_);
lean_dec(v___x_758_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec(v___x_747_);
lean_inc_ref(v_x_748_);
lean_inc_ref(v___x_741_);
v___x_761_ = lean_array_push(v___x_741_, v_x_748_);
v___x_762_ = l_Lean_Meta_mkLambdaFVars(v___x_761_, v___x_742_, v___x_737_, v___x_738_, v___x_737_, v___x_738_, v___x_739_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec_ref(v___x_761_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref(v___x_762_);
v___x_764_ = lean_obj_once(&l_mkCtorIdx___lam__0___closed__0, &l_mkCtorIdx___lam__0___closed__0_once, _init_l_mkCtorIdx___lam__0___closed__0);
v___x_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
lean_ctor_set(v___x_765_, 1, v___x_743_);
v___x_766_ = l_Lean_mkConst(v___x_744_, v___x_765_);
v___x_767_ = l_Lean_mkAppN(v___x_766_, v___x_745_);
v___x_768_ = l_Lean_Expr_app___override(v___x_767_, v_a_763_);
v___x_769_ = l_Lean_mkAppN(v___x_768_, v___x_741_);
lean_dec_ref(v___x_741_);
lean_inc_ref(v_x_748_);
v___x_770_ = l_Lean_Expr_app___override(v___x_769_, v_x_748_);
v___x_771_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_738_, v___x_745_, v_ctors_746_, v___x_770_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref(v___x_771_);
v_value_755_ = v_a_772_;
goto v___jp_754_;
}
else
{
lean_dec_ref(v_x_748_);
lean_dec_ref(v_xs_736_);
return v___x_771_;
}
}
else
{
lean_dec_ref(v_x_748_);
lean_dec(v_ctors_746_);
lean_dec(v___x_744_);
lean_dec(v___x_743_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v_xs_736_);
return v___x_762_;
}
}
else
{
lean_object* v___x_773_; 
lean_dec(v_ctors_746_);
lean_dec(v___x_744_);
lean_dec(v___x_743_);
lean_dec_ref(v___x_742_);
lean_dec_ref(v___x_741_);
v___x_773_ = l_Lean_mkRawNatLit(v___x_747_);
v_value_755_ = v___x_773_;
goto v___jp_754_;
}
v___jp_754_:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_array_push(v_xs_736_, v_x_748_);
v___x_757_ = l_Lean_Meta_mkLambdaFVars(v___x_756_, v_value_755_, v___x_737_, v___x_738_, v___x_737_, v___x_738_, v___x_739_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec_ref(v___x_756_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_774_ = _args[0];
lean_object* v___x_775_ = _args[1];
lean_object* v___x_776_ = _args[2];
lean_object* v___x_777_ = _args[3];
lean_object* v_val_778_ = _args[4];
lean_object* v___x_779_ = _args[5];
lean_object* v___x_780_ = _args[6];
lean_object* v___x_781_ = _args[7];
lean_object* v___x_782_ = _args[8];
lean_object* v___x_783_ = _args[9];
lean_object* v_ctors_784_ = _args[10];
lean_object* v___x_785_ = _args[11];
lean_object* v_x_786_ = _args[12];
lean_object* v___y_787_ = _args[13];
lean_object* v___y_788_ = _args[14];
lean_object* v___y_789_ = _args[15];
lean_object* v___y_790_ = _args[16];
lean_object* v___y_791_ = _args[17];
_start:
{
uint8_t v___x_34952__boxed_792_; uint8_t v___x_34953__boxed_793_; uint8_t v___x_34954__boxed_794_; lean_object* v_res_795_; 
v___x_34952__boxed_792_ = lean_unbox(v___x_775_);
v___x_34953__boxed_793_ = lean_unbox(v___x_776_);
v___x_34954__boxed_794_ = lean_unbox(v___x_777_);
v_res_795_ = l_mkCtorIdx___lam__0(v_xs_774_, v___x_34952__boxed_792_, v___x_34953__boxed_793_, v___x_34954__boxed_794_, v_val_778_, v___x_779_, v___x_780_, v___x_781_, v___x_782_, v___x_783_, v_ctors_784_, v___x_785_, v_x_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec_ref(v___y_787_);
lean_dec_ref(v___x_783_);
lean_dec_ref(v_val_778_);
return v_res_795_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_796_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
v___x_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
return v___x_798_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_799_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
lean_ctor_set(v___x_801_, 3, v___x_800_);
lean_ctor_set(v___x_801_, 4, v___x_799_);
lean_ctor_set(v___x_801_, 5, v___x_799_);
lean_ctor_set(v___x_801_, 6, v___x_799_);
lean_ctor_set(v___x_801_, 7, v___x_799_);
lean_ctor_set(v___x_801_, 8, v___x_799_);
lean_ctor_set(v___x_801_, 9, v___x_799_);
return v___x_801_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_802_ = lean_unsigned_to_nat(32u);
v___x_803_ = lean_mk_empty_array_with_capacity(v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_805_ = ((size_t)5ULL);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_unsigned_to_nat(32u);
v___x_808_ = lean_mk_empty_array_with_capacity(v___x_807_);
v___x_809_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
v___x_810_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___x_808_);
lean_ctor_set(v___x_810_, 2, v___x_806_);
lean_ctor_set(v___x_810_, 3, v___x_806_);
lean_ctor_set_usize(v___x_810_, 4, v___x_805_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_811_ = lean_box(1);
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_814_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v___x_812_);
lean_ctor_set(v___x_814_, 2, v___x_811_);
return v___x_814_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6));
v___x_817_ = l_Lean_stringToMessageData(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8));
v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
return v___x_820_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; 
v___x_822_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10));
v___x_823_ = l_Lean_stringToMessageData(v___x_822_);
return v___x_823_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12));
v___x_826_ = l_Lean_stringToMessageData(v___x_825_);
return v___x_826_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14));
v___x_829_ = l_Lean_stringToMessageData(v___x_828_);
return v___x_829_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16));
v___x_832_ = l_Lean_stringToMessageData(v___x_831_);
return v___x_832_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_834_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18));
v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object* v_msg_836_, lean_object* v_declHint_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; lean_object* v_env_841_; uint8_t v___x_842_; 
v___x_840_ = lean_st_ref_get(v___y_838_);
v_env_841_ = lean_ctor_get(v___x_840_, 0);
lean_inc_ref(v_env_841_);
lean_dec(v___x_840_);
v___x_842_ = l_Lean_Name_isAnonymous(v_declHint_837_);
if (v___x_842_ == 0)
{
uint8_t v_isExporting_843_; 
v_isExporting_843_ = lean_ctor_get_uint8(v_env_841_, sizeof(void*)*8);
if (v_isExporting_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec_ref(v_env_841_);
lean_dec(v_declHint_837_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_msg_836_);
return v___x_844_;
}
else
{
lean_object* v___x_845_; uint8_t v___x_846_; 
lean_inc_ref(v_env_841_);
v___x_845_ = l_Lean_Environment_setExporting(v_env_841_, v___x_842_);
lean_inc(v_declHint_837_);
lean_inc_ref(v___x_845_);
v___x_846_ = l_Lean_Environment_contains(v___x_845_, v_declHint_837_, v_isExporting_843_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec_ref(v___x_845_);
lean_dec_ref(v_env_841_);
lean_dec(v_declHint_837_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_msg_836_);
return v___x_847_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v_c_853_; lean_object* v___x_854_; 
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
v___x_849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
v___x_850_ = l_Lean_Options_empty;
v___x_851_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_851_, 0, v___x_845_);
lean_ctor_set(v___x_851_, 1, v___x_848_);
lean_ctor_set(v___x_851_, 2, v___x_849_);
lean_ctor_set(v___x_851_, 3, v___x_850_);
lean_inc(v_declHint_837_);
v___x_852_ = l_Lean_MessageData_ofConstName(v_declHint_837_, v___x_842_);
v_c_853_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_853_, 0, v___x_851_);
lean_ctor_set(v_c_853_, 1, v___x_852_);
v___x_854_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_841_, v_declHint_837_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref(v_env_841_);
lean_dec(v_declHint_837_);
v___x_855_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
lean_ctor_set(v___x_856_, 1, v_c_853_);
v___x_857_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
v___x_858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_856_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
v___x_859_ = l_Lean_MessageData_note(v___x_858_);
v___x_860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_860_, 0, v_msg_836_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
return v___x_861_;
}
else
{
lean_object* v_val_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_897_; 
v_val_862_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_897_ == 0)
{
v___x_864_ = v___x_854_;
v_isShared_865_ = v_isSharedCheck_897_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_val_862_);
lean_dec(v___x_854_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_897_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v_mod_869_; uint8_t v___x_870_; 
v___x_866_ = lean_box(0);
v___x_867_ = l_Lean_Environment_header(v_env_841_);
lean_dec_ref(v_env_841_);
v___x_868_ = l_Lean_EnvironmentHeader_moduleNames(v___x_867_);
v_mod_869_ = lean_array_get(v___x_866_, v___x_868_, v_val_862_);
lean_dec(v_val_862_);
lean_dec_ref(v___x_868_);
v___x_870_ = l_Lean_isPrivateName(v_declHint_837_);
lean_dec(v_declHint_837_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_882_; 
v___x_871_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v_c_853_);
v___x_873_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
v___x_874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_872_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Lean_MessageData_ofName(v_mod_869_);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
v___x_878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
v___x_879_ = l_Lean_MessageData_note(v___x_878_);
v___x_880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_880_, 0, v_msg_836_);
lean_ctor_set(v___x_880_, 1, v___x_879_);
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 0);
lean_ctor_set(v___x_864_, 0, v___x_880_);
v___x_882_ = v___x_864_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v___x_880_);
v___x_882_ = v_reuseFailAlloc_883_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
return v___x_882_;
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_895_; 
v___x_884_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v_c_853_);
v___x_886_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_MessageData_ofName(v_mod_869_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
v___x_891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
v___x_892_ = l_Lean_MessageData_note(v___x_891_);
v___x_893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_893_, 0, v_msg_836_);
lean_ctor_set(v___x_893_, 1, v___x_892_);
if (v_isShared_865_ == 0)
{
lean_ctor_set_tag(v___x_864_, 0);
lean_ctor_set(v___x_864_, 0, v___x_893_);
v___x_895_ = v___x_864_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_898_; 
lean_dec_ref(v_env_841_);
lean_dec(v_declHint_837_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_msg_836_);
return v___x_898_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object* v_msg_899_, lean_object* v_declHint_900_, lean_object* v___y_901_, lean_object* v___y_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_899_, v_declHint_900_, v___y_901_);
lean_dec(v___y_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object* v_msg_904_, lean_object* v_declHint_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_921_; 
v___x_911_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_904_, v_declHint_905_, v___y_909_);
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_921_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_916_ = l_Lean_unknownIdentifierMessageTag;
v___x_917_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_916_);
lean_ctor_set(v___x_917_, 1, v_a_912_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_917_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object* v_msg_922_, lean_object* v_declHint_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_922_, v_declHint_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
lean_dec(v___y_927_);
lean_dec_ref(v___y_926_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object* v_ref_930_, lean_object* v_msg_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_fileName_937_; lean_object* v_fileMap_938_; lean_object* v_options_939_; lean_object* v_currRecDepth_940_; lean_object* v_maxRecDepth_941_; lean_object* v_ref_942_; lean_object* v_currNamespace_943_; lean_object* v_openDecls_944_; lean_object* v_initHeartbeats_945_; lean_object* v_maxHeartbeats_946_; lean_object* v_quotContext_947_; lean_object* v_currMacroScope_948_; uint8_t v_diag_949_; lean_object* v_cancelTk_x3f_950_; uint8_t v_suppressElabErrors_951_; lean_object* v_inheritedTraceOptions_952_; lean_object* v_ref_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_fileName_937_ = lean_ctor_get(v___y_934_, 0);
v_fileMap_938_ = lean_ctor_get(v___y_934_, 1);
v_options_939_ = lean_ctor_get(v___y_934_, 2);
v_currRecDepth_940_ = lean_ctor_get(v___y_934_, 3);
v_maxRecDepth_941_ = lean_ctor_get(v___y_934_, 4);
v_ref_942_ = lean_ctor_get(v___y_934_, 5);
v_currNamespace_943_ = lean_ctor_get(v___y_934_, 6);
v_openDecls_944_ = lean_ctor_get(v___y_934_, 7);
v_initHeartbeats_945_ = lean_ctor_get(v___y_934_, 8);
v_maxHeartbeats_946_ = lean_ctor_get(v___y_934_, 9);
v_quotContext_947_ = lean_ctor_get(v___y_934_, 10);
v_currMacroScope_948_ = lean_ctor_get(v___y_934_, 11);
v_diag_949_ = lean_ctor_get_uint8(v___y_934_, sizeof(void*)*14);
v_cancelTk_x3f_950_ = lean_ctor_get(v___y_934_, 12);
v_suppressElabErrors_951_ = lean_ctor_get_uint8(v___y_934_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_952_ = lean_ctor_get(v___y_934_, 13);
v_ref_953_ = l_Lean_replaceRef(v_ref_930_, v_ref_942_);
lean_inc_ref(v_inheritedTraceOptions_952_);
lean_inc(v_cancelTk_x3f_950_);
lean_inc(v_currMacroScope_948_);
lean_inc(v_quotContext_947_);
lean_inc(v_maxHeartbeats_946_);
lean_inc(v_initHeartbeats_945_);
lean_inc(v_openDecls_944_);
lean_inc(v_currNamespace_943_);
lean_inc(v_maxRecDepth_941_);
lean_inc(v_currRecDepth_940_);
lean_inc_ref(v_options_939_);
lean_inc_ref(v_fileMap_938_);
lean_inc_ref(v_fileName_937_);
v___x_954_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_954_, 0, v_fileName_937_);
lean_ctor_set(v___x_954_, 1, v_fileMap_938_);
lean_ctor_set(v___x_954_, 2, v_options_939_);
lean_ctor_set(v___x_954_, 3, v_currRecDepth_940_);
lean_ctor_set(v___x_954_, 4, v_maxRecDepth_941_);
lean_ctor_set(v___x_954_, 5, v_ref_953_);
lean_ctor_set(v___x_954_, 6, v_currNamespace_943_);
lean_ctor_set(v___x_954_, 7, v_openDecls_944_);
lean_ctor_set(v___x_954_, 8, v_initHeartbeats_945_);
lean_ctor_set(v___x_954_, 9, v_maxHeartbeats_946_);
lean_ctor_set(v___x_954_, 10, v_quotContext_947_);
lean_ctor_set(v___x_954_, 11, v_currMacroScope_948_);
lean_ctor_set(v___x_954_, 12, v_cancelTk_x3f_950_);
lean_ctor_set(v___x_954_, 13, v_inheritedTraceOptions_952_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*14, v_diag_949_);
lean_ctor_set_uint8(v___x_954_, sizeof(void*)*14 + 1, v_suppressElabErrors_951_);
v___x_955_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_931_, v___y_932_, v___y_933_, v___x_954_, v___y_935_);
lean_dec_ref(v___x_954_);
return v___x_955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object* v_ref_956_, lean_object* v_msg_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_956_, v_msg_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v_ref_956_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object* v_ref_964_, lean_object* v_msg_965_, lean_object* v_declHint_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; lean_object* v_a_973_; lean_object* v___x_974_; 
v___x_972_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_965_, v_declHint_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
v_a_973_ = lean_ctor_get(v___x_972_, 0);
lean_inc(v_a_973_);
lean_dec_ref(v___x_972_);
v___x_974_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_964_, v_a_973_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object* v_ref_975_, lean_object* v_msg_976_, lean_object* v_declHint_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_975_, v_msg_976_, v_declHint_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v_ref_975_);
return v_res_983_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_986_ = l_Lean_stringToMessageData(v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_987_, lean_object* v_constName_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; uint8_t v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_994_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_995_ = 0;
lean_inc(v_constName_988_);
v___x_996_ = l_Lean_MessageData_ofConstName(v_constName_988_, v___x_995_);
v___x_997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_997_, 0, v___x_994_);
lean_ctor_set(v___x_997_, 1, v___x_996_);
v___x_998_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__1);
v___x_999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_997_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
v___x_1000_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_987_, v___x_999_, v_constName_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1001_, lean_object* v_constName_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1001_, v_constName_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v_ref_1001_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_ref_1015_; lean_object* v___x_1016_; 
v_ref_1015_ = lean_ctor_get(v___y_1012_, 5);
v___x_1016_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1015_, v_constName_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec_ref(v___y_1018_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(lean_object* v_constName_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v___x_1030_; lean_object* v_env_1031_; uint8_t v___x_1032_; lean_object* v___x_1033_; 
v___x_1030_ = lean_st_ref_get(v___y_1028_);
v_env_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc_ref(v_env_1031_);
lean_dec(v___x_1030_);
v___x_1032_ = 0;
lean_inc(v_constName_1024_);
v___x_1033_ = l_Lean_Environment_find_x3f(v_env_1031_, v_constName_1024_, v___x_1032_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
return v___x_1034_;
}
else
{
lean_object* v_val_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec(v_constName_1024_);
v_val_1035_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1033_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_val_1035_);
lean_dec(v___x_1033_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_val_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00mkCtorIdx_spec__2___boxed(lean_object* v_constName_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_res_1049_; 
v_res_1049_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_constName_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
return v_res_1049_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(uint8_t v___x_1050_, lean_object* v_x_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1057_ = 1;
v___x_1058_ = lean_box(v___x_1057_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
else
{
lean_object* v_head_1060_; lean_object* v_tail_1061_; lean_object* v___x_1062_; 
v_head_1060_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_head_1060_);
v_tail_1061_ = lean_ctor_get(v_x_1051_, 1);
lean_inc(v_tail_1061_);
lean_dec_ref(v_x_1051_);
v___x_1062_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_head_1060_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_);
if (lean_obj_tag(v___x_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1083_; 
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1065_ = v___x_1062_;
v_isShared_1066_ = v_isSharedCheck_1083_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1083_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___y_1068_; uint8_t v_a_1069_; 
if (lean_obj_tag(v_a_1063_) == 6)
{
lean_object* v_val_1071_; lean_object* v_numFields_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v_val_1071_ = lean_ctor_get(v_a_1063_, 0);
lean_inc_ref(v_val_1071_);
lean_dec_ref(v_a_1063_);
v_numFields_1072_ = lean_ctor_get(v_val_1071_, 4);
lean_inc(v_numFields_1072_);
lean_dec_ref(v_val_1071_);
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_nat_dec_eq(v_numFields_1072_, v___x_1073_);
lean_dec(v_numFields_1072_);
v___x_1075_ = lean_box(v___x_1074_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1075_);
v___x_1077_ = v___x_1065_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
v___y_1068_ = v___x_1077_;
v_a_1069_ = v___x_1074_;
goto v___jp_1067_;
}
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_dec(v_a_1063_);
v___x_1079_ = lean_box(v___x_1050_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 0, v___x_1079_);
v___x_1081_ = v___x_1065_;
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
v___y_1068_ = v___x_1081_;
v_a_1069_ = v___x_1050_;
goto v___jp_1067_;
}
}
v___jp_1067_:
{
if (v_a_1069_ == 0)
{
lean_dec(v_tail_1061_);
return v___y_1068_;
}
else
{
lean_dec_ref(v___y_1068_);
v_x_1051_ = v_tail_1061_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_dec(v_tail_1061_);
v_a_1084_ = lean_ctor_get(v___x_1062_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1062_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1062_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1062_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13___boxed(lean_object* v___x_1092_, lean_object* v_x_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
uint8_t v___x_35472__boxed_1099_; lean_object* v_res_1100_; 
v___x_35472__boxed_1099_ = lean_unbox(v___x_1092_);
v_res_1100_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v___x_35472__boxed_1099_, v_x_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9(lean_object* v_declName_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_declName_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1163_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1110_ = v___x_1107_;
v_isShared_1111_ = v_isSharedCheck_1163_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1107_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1163_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
if (lean_obj_tag(v_a_1108_) == 5)
{
lean_object* v_val_1112_; lean_object* v_toConstantVal_1113_; lean_object* v_numParams_1114_; lean_object* v_numIndices_1115_; lean_object* v_ctors_1116_; uint8_t v_isRec_1117_; uint8_t v_isUnsafe_1118_; lean_object* v_type_1119_; uint8_t v___x_1120_; 
v_val_1112_ = lean_ctor_get(v_a_1108_, 0);
lean_inc_ref(v_val_1112_);
lean_dec_ref(v_a_1108_);
v_toConstantVal_1113_ = lean_ctor_get(v_val_1112_, 0);
v_numParams_1114_ = lean_ctor_get(v_val_1112_, 1);
lean_inc(v_numParams_1114_);
v_numIndices_1115_ = lean_ctor_get(v_val_1112_, 2);
lean_inc(v_numIndices_1115_);
v_ctors_1116_ = lean_ctor_get(v_val_1112_, 4);
lean_inc(v_ctors_1116_);
v_isRec_1117_ = lean_ctor_get_uint8(v_val_1112_, sizeof(void*)*6);
v_isUnsafe_1118_ = lean_ctor_get_uint8(v_val_1112_, sizeof(void*)*6 + 1);
v_type_1119_ = lean_ctor_get(v_toConstantVal_1113_, 2);
v___x_1120_ = l_Lean_Expr_isProp(v_type_1119_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1121_ = l_Lean_InductiveVal_numTypeFormers(v_val_1112_);
lean_dec_ref(v_val_1112_);
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_dec_eq(v___x_1121_, v___x_1122_);
lean_dec(v___x_1121_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_dec(v_ctors_1116_);
lean_dec(v_numIndices_1115_);
lean_dec(v_numParams_1114_);
v___x_1124_ = lean_box(v___x_1123_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1124_);
v___x_1126_ = v___x_1110_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
else
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_nat_dec_eq(v_numIndices_1115_, v___x_1128_);
lean_dec(v_numIndices_1115_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec(v_ctors_1116_);
lean_dec(v_numParams_1114_);
v___x_1130_ = lean_box(v___x_1129_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1130_);
v___x_1132_ = v___x_1110_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
uint8_t v___x_1134_; 
v___x_1134_ = lean_nat_dec_eq(v_numParams_1114_, v___x_1128_);
lean_dec(v_numParams_1114_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
lean_dec(v_ctors_1116_);
v___x_1135_ = lean_box(v___x_1134_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1135_);
v___x_1137_ = v___x_1110_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
else
{
uint8_t v___x_1139_; 
v___x_1139_ = l_List_isEmpty___redArg(v_ctors_1116_);
if (v___x_1139_ == 0)
{
if (v_isRec_1117_ == 0)
{
if (v_isUnsafe_1118_ == 0)
{
lean_object* v___x_1140_; 
lean_del_object(v___x_1110_);
v___x_1140_ = l_List_allM___at___00Lean_isEnumType___at___00mkCtorIdx_spec__9_spec__13(v_isUnsafe_1118_, v_ctors_1116_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
return v___x_1140_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_dec(v_ctors_1116_);
v___x_1141_ = lean_box(v_isRec_1117_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1141_);
v___x_1143_ = v___x_1110_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
lean_dec(v_ctors_1116_);
v___x_1145_ = lean_box(v___x_1139_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1145_);
v___x_1147_ = v___x_1110_;
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
lean_dec(v_ctors_1116_);
v___x_1149_ = lean_box(v___x_1120_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1149_);
v___x_1151_ = v___x_1110_;
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
}
}
}
else
{
uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
lean_dec(v_ctors_1116_);
lean_dec(v_numIndices_1115_);
lean_dec(v_numParams_1114_);
lean_dec_ref(v_val_1112_);
v___x_1153_ = 0;
v___x_1154_ = lean_box(v___x_1153_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1154_);
v___x_1156_ = v___x_1110_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
uint8_t v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_dec(v_a_1108_);
v___x_1158_ = 0;
v___x_1159_ = lean_box(v___x_1158_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 0, v___x_1159_);
v___x_1161_ = v___x_1110_;
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
else
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1171_; 
v_a_1164_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1166_ = v___x_1107_;
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1107_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1171_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1169_; 
if (v_isShared_1167_ == 0)
{
v___x_1169_ = v___x_1166_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00mkCtorIdx_spec__9___boxed(lean_object* v_declName_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_){
_start:
{
lean_object* v_res_1178_; 
v_res_1178_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_declName_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1175_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
return v_res_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_1179_, lean_object* v_b_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v___x_1186_; 
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
lean_inc(v___y_1182_);
lean_inc_ref(v___y_1181_);
v___x_1186_ = lean_apply_6(v_k_1179_, v_b_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, lean_box(0));
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_1187_, lean_object* v_b_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_1187_, v_b_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_1195_, uint8_t v_bi_1196_, lean_object* v_type_1197_, lean_object* v_k_1198_, uint8_t v_kind_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v___f_1205_; lean_object* v___x_1206_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_1205_, 0, v_k_1198_);
v___x_1206_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_1195_, v_bi_1196_, v_type_1197_, v___f_1205_, v_kind_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
v_a_1215_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1206_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1206_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_1223_, lean_object* v_bi_1224_, lean_object* v_type_1225_, lean_object* v_k_1226_, lean_object* v_kind_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v_bi_boxed_1233_; uint8_t v_kind_boxed_1234_; lean_object* v_res_1235_; 
v_bi_boxed_1233_ = lean_unbox(v_bi_1224_);
v_kind_boxed_1234_ = lean_unbox(v_kind_1227_);
v_res_1235_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1223_, v_bi_boxed_1233_, v_type_1225_, v_k_1226_, v_kind_boxed_1234_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(lean_object* v_name_1236_, lean_object* v_type_1237_, lean_object* v_k_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v___x_1244_; uint8_t v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = 0;
v___x_1245_ = 0;
v___x_1246_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_1236_, v___x_1244_, v_type_1237_, v_k_1238_, v___x_1245_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_1247_, lean_object* v_type_1248_, lean_object* v_k_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_1247_, v_type_1248_, v_k_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(lean_object* v_env_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v___x_1260_; lean_object* v_nextMacroScope_1261_; lean_object* v_ngen_1262_; lean_object* v_auxDeclNGen_1263_; lean_object* v_traceState_1264_; lean_object* v_messages_1265_; lean_object* v_infoState_1266_; lean_object* v_snapshotTasks_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1293_; 
v___x_1260_ = lean_st_ref_take(v___y_1258_);
v_nextMacroScope_1261_ = lean_ctor_get(v___x_1260_, 1);
v_ngen_1262_ = lean_ctor_get(v___x_1260_, 2);
v_auxDeclNGen_1263_ = lean_ctor_get(v___x_1260_, 3);
v_traceState_1264_ = lean_ctor_get(v___x_1260_, 4);
v_messages_1265_ = lean_ctor_get(v___x_1260_, 6);
v_infoState_1266_ = lean_ctor_get(v___x_1260_, 7);
v_snapshotTasks_1267_ = lean_ctor_get(v___x_1260_, 8);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1293_ == 0)
{
lean_object* v_unused_1294_; lean_object* v_unused_1295_; 
v_unused_1294_ = lean_ctor_get(v___x_1260_, 5);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v___x_1260_, 0);
lean_dec(v_unused_1295_);
v___x_1269_ = v___x_1260_;
v_isShared_1270_ = v_isSharedCheck_1293_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_snapshotTasks_1267_);
lean_inc(v_infoState_1266_);
lean_inc(v_messages_1265_);
lean_inc(v_traceState_1264_);
lean_inc(v_auxDeclNGen_1263_);
lean_inc(v_ngen_1262_);
lean_inc(v_nextMacroScope_1261_);
lean_dec(v___x_1260_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1293_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 5, v___x_1271_);
lean_ctor_set(v___x_1269_, 0, v_env_1256_);
v___x_1273_ = v___x_1269_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_env_1256_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_nextMacroScope_1261_);
lean_ctor_set(v_reuseFailAlloc_1292_, 2, v_ngen_1262_);
lean_ctor_set(v_reuseFailAlloc_1292_, 3, v_auxDeclNGen_1263_);
lean_ctor_set(v_reuseFailAlloc_1292_, 4, v_traceState_1264_);
lean_ctor_set(v_reuseFailAlloc_1292_, 5, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1292_, 6, v_messages_1265_);
lean_ctor_set(v_reuseFailAlloc_1292_, 7, v_infoState_1266_);
lean_ctor_set(v_reuseFailAlloc_1292_, 8, v_snapshotTasks_1267_);
v___x_1273_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_mctx_1276_; lean_object* v_zetaDeltaFVarIds_1277_; lean_object* v_postponed_1278_; lean_object* v_diag_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1290_; 
v___x_1274_ = lean_st_ref_set(v___y_1258_, v___x_1273_);
v___x_1275_ = lean_st_ref_take(v___y_1257_);
v_mctx_1276_ = lean_ctor_get(v___x_1275_, 0);
v_zetaDeltaFVarIds_1277_ = lean_ctor_get(v___x_1275_, 2);
v_postponed_1278_ = lean_ctor_get(v___x_1275_, 3);
v_diag_1279_ = lean_ctor_get(v___x_1275_, 4);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1275_);
if (v_isSharedCheck_1290_ == 0)
{
lean_object* v_unused_1291_; 
v_unused_1291_ = lean_ctor_get(v___x_1275_, 1);
lean_dec(v_unused_1291_);
v___x_1281_ = v___x_1275_;
v_isShared_1282_ = v_isSharedCheck_1290_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_diag_1279_);
lean_inc(v_postponed_1278_);
lean_inc(v_zetaDeltaFVarIds_1277_);
lean_inc(v_mctx_1276_);
lean_dec(v___x_1275_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1290_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1283_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_mctx_1276_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_zetaDeltaFVarIds_1277_);
lean_ctor_set(v_reuseFailAlloc_1289_, 3, v_postponed_1278_);
lean_ctor_set(v_reuseFailAlloc_1289_, 4, v_diag_1279_);
v___x_1285_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = lean_st_ref_set(v___y_1257_, v___x_1285_);
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1287_);
return v___x_1288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object* v_env_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_1296_, v___y_1297_, v___y_1298_);
lean_dec(v___y_1298_);
lean_dec(v___y_1297_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(lean_object* v_declName_1301_, lean_object* v_entry_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_env_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1308_ = lean_st_ref_get(v___y_1306_);
v_env_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_env_1309_);
lean_dec(v___x_1308_);
v___x_1310_ = l_Lean_Linter_deprecatedAttr;
v___x_1311_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1310_, v_env_1309_, v_declName_1301_, v_entry_1302_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1321_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1321_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1321_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set_tag(v___x_1314_, 3);
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = l_Lean_MessageData_ofFormat(v___x_1317_);
v___x_1319_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v___x_1318_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
return v___x_1319_;
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1323_; 
v_a_1322_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1322_);
lean_dec_ref(v___x_1311_);
v___x_1323_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_a_1322_, v___y_1304_, v___y_1306_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11___boxed(lean_object* v_declName_1324_, lean_object* v_entry_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v_declName_1324_, v_entry_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(lean_object* v_declName_1332_, uint8_t v_s_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___x_1337_; lean_object* v_env_1338_; lean_object* v_nextMacroScope_1339_; lean_object* v_ngen_1340_; lean_object* v_auxDeclNGen_1341_; lean_object* v_traceState_1342_; lean_object* v_messages_1343_; lean_object* v_infoState_1344_; lean_object* v_snapshotTasks_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1374_; 
v___x_1337_ = lean_st_ref_take(v___y_1335_);
v_env_1338_ = lean_ctor_get(v___x_1337_, 0);
v_nextMacroScope_1339_ = lean_ctor_get(v___x_1337_, 1);
v_ngen_1340_ = lean_ctor_get(v___x_1337_, 2);
v_auxDeclNGen_1341_ = lean_ctor_get(v___x_1337_, 3);
v_traceState_1342_ = lean_ctor_get(v___x_1337_, 4);
v_messages_1343_ = lean_ctor_get(v___x_1337_, 6);
v_infoState_1344_ = lean_ctor_get(v___x_1337_, 7);
v_snapshotTasks_1345_ = lean_ctor_get(v___x_1337_, 8);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1337_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v___x_1337_, 5);
lean_dec(v_unused_1375_);
v___x_1347_ = v___x_1337_;
v_isShared_1348_ = v_isSharedCheck_1374_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snapshotTasks_1345_);
lean_inc(v_infoState_1344_);
lean_inc(v_messages_1343_);
lean_inc(v_traceState_1342_);
lean_inc(v_auxDeclNGen_1341_);
lean_inc(v_ngen_1340_);
lean_inc(v_nextMacroScope_1339_);
lean_inc(v_env_1338_);
lean_dec(v___x_1337_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1374_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
uint8_t v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1349_ = 0;
v___x_1350_ = lean_box(0);
v___x_1351_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1338_, v_declName_1332_, v_s_1333_, v___x_1349_, v___x_1350_);
v___x_1352_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 5, v___x_1352_);
lean_ctor_set(v___x_1347_, 0, v___x_1351_);
v___x_1354_ = v___x_1347_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_nextMacroScope_1339_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_ngen_1340_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_auxDeclNGen_1341_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v_traceState_1342_);
lean_ctor_set(v_reuseFailAlloc_1373_, 5, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1373_, 6, v_messages_1343_);
lean_ctor_set(v_reuseFailAlloc_1373_, 7, v_infoState_1344_);
lean_ctor_set(v_reuseFailAlloc_1373_, 8, v_snapshotTasks_1345_);
v___x_1354_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_mctx_1357_; lean_object* v_zetaDeltaFVarIds_1358_; lean_object* v_postponed_1359_; lean_object* v_diag_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1371_; 
v___x_1355_ = lean_st_ref_set(v___y_1335_, v___x_1354_);
v___x_1356_ = lean_st_ref_take(v___y_1334_);
v_mctx_1357_ = lean_ctor_get(v___x_1356_, 0);
v_zetaDeltaFVarIds_1358_ = lean_ctor_get(v___x_1356_, 2);
v_postponed_1359_ = lean_ctor_get(v___x_1356_, 3);
v_diag_1360_ = lean_ctor_get(v___x_1356_, 4);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v___x_1356_, 1);
lean_dec(v_unused_1372_);
v___x_1362_ = v___x_1356_;
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_diag_1360_);
lean_inc(v_postponed_1359_);
lean_inc(v_zetaDeltaFVarIds_1358_);
lean_inc(v_mctx_1357_);
lean_dec(v___x_1356_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1371_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1364_; lean_object* v___x_1366_; 
v___x_1364_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1363_ == 0)
{
lean_ctor_set(v___x_1362_, 1, v___x_1364_);
v___x_1366_ = v___x_1362_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_mctx_1357_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1364_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_zetaDeltaFVarIds_1358_);
lean_ctor_set(v_reuseFailAlloc_1370_, 3, v_postponed_1359_);
lean_ctor_set(v_reuseFailAlloc_1370_, 4, v_diag_1360_);
v___x_1366_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1367_ = lean_st_ref_set(v___y_1334_, v___x_1366_);
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
return v___x_1369_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object* v_declName_1376_, lean_object* v_s_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_s_boxed_1381_; lean_object* v_res_1382_; 
v_s_boxed_1381_ = lean_unbox(v_s_1377_);
v_res_1382_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1376_, v_s_boxed_1381_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec(v___y_1378_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(lean_object* v_declName_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
uint8_t v___x_1389_; lean_object* v___x_1390_; 
v___x_1389_ = 0;
v___x_1390_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_1383_, v___x_1389_, v___y_1385_, v___y_1387_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10___boxed(lean_object* v_declName_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v_declName_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1(lean_object* v___x_1404_, lean_object* v___x_1405_, lean_object* v_xs_1406_, uint8_t v___x_1407_, uint8_t v___x_1408_, lean_object* v_val_1409_, lean_object* v___x_1410_, lean_object* v___x_1411_, lean_object* v___x_1412_, lean_object* v___x_1413_, lean_object* v_ctors_1414_, lean_object* v___x_1415_, lean_object* v___x_1416_, lean_object* v_levelParams_1417_, lean_object* v_indName_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___x_1515_; 
lean_inc_ref(v___x_1405_);
lean_inc_ref(v___x_1404_);
v___x_1515_ = l_Lean_mkArrow(v___x_1404_, v___x_1405_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1515_);
v___x_1517_ = 1;
v___x_1518_ = l_Lean_Meta_mkForallFVars(v_xs_1406_, v_a_1516_, v___x_1407_, v___x_1408_, v___x_1408_, v___x_1517_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v___x_1518_);
v___x_1520_ = lean_box(v___x_1407_);
v___x_1521_ = lean_box(v___x_1408_);
v___x_1522_ = lean_box(v___x_1517_);
lean_inc(v___x_1411_);
lean_inc_ref(v_val_1409_);
v___f_1523_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1523_, 0, v_xs_1406_);
lean_closure_set(v___f_1523_, 1, v___x_1520_);
lean_closure_set(v___f_1523_, 2, v___x_1521_);
lean_closure_set(v___f_1523_, 3, v___x_1522_);
lean_closure_set(v___f_1523_, 4, v_val_1409_);
lean_closure_set(v___f_1523_, 5, v___x_1410_);
lean_closure_set(v___f_1523_, 6, v___x_1405_);
lean_closure_set(v___f_1523_, 7, v___x_1411_);
lean_closure_set(v___f_1523_, 8, v___x_1412_);
lean_closure_set(v___f_1523_, 9, v___x_1413_);
lean_closure_set(v___f_1523_, 10, v_ctors_1414_);
lean_closure_set(v___f_1523_, 11, v___x_1415_);
v___x_1524_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__3));
v___x_1525_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v___x_1524_, v___x_1404_, v___f_1523_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1527_; lean_object* v_env_1528_; uint32_t v___x_1529_; uint32_t v___x_1530_; uint32_t v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1735_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc_n(v_a_1526_, 2);
lean_dec_ref(v___x_1525_);
v___x_1527_ = lean_st_ref_get(v___y_1422_);
v_env_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc_ref(v_env_1528_);
lean_dec(v___x_1527_);
v___x_1529_ = l_Lean_getMaxHeight(v_env_1528_, v_a_1526_);
v___x_1530_ = 1;
v___x_1531_ = lean_uint32_add(v___x_1529_, v___x_1530_);
v___x_1532_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1532_, 0, v___x_1531_);
lean_inc(v_a_1519_);
lean_inc(v_levelParams_1417_);
lean_inc(v___x_1416_);
v___x_1533_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1416_, v_levelParams_1417_, v_a_1519_, v_a_1526_, v___x_1532_, v___y_1422_);
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1735_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1735_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 1);
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
lean_object* v___y_1541_; lean_object* v___y_1542_; lean_object* v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1618_; lean_object* v___y_1619_; lean_object* v___y_1620_; lean_object* v___y_1621_; lean_object* v___x_1660_; 
lean_inc_ref(v___x_1539_);
v___x_1660_ = l_Lean_addDecl(v___x_1539_, v___x_1407_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1660_) == 0)
{
lean_object* v___x_1661_; lean_object* v_env_1662_; lean_object* v_nextMacroScope_1663_; lean_object* v_ngen_1664_; lean_object* v_auxDeclNGen_1665_; lean_object* v_traceState_1666_; lean_object* v_messages_1667_; lean_object* v_infoState_1668_; lean_object* v_snapshotTasks_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1732_; 
lean_dec_ref(v___x_1660_);
v___x_1661_ = lean_st_ref_take(v___y_1422_);
v_env_1662_ = lean_ctor_get(v___x_1661_, 0);
v_nextMacroScope_1663_ = lean_ctor_get(v___x_1661_, 1);
v_ngen_1664_ = lean_ctor_get(v___x_1661_, 2);
v_auxDeclNGen_1665_ = lean_ctor_get(v___x_1661_, 3);
v_traceState_1666_ = lean_ctor_get(v___x_1661_, 4);
v_messages_1667_ = lean_ctor_get(v___x_1661_, 6);
v_infoState_1668_ = lean_ctor_get(v___x_1661_, 7);
v_snapshotTasks_1669_ = lean_ctor_get(v___x_1661_, 8);
v_isSharedCheck_1732_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1732_ == 0)
{
lean_object* v_unused_1733_; 
v_unused_1733_ = lean_ctor_get(v___x_1661_, 5);
lean_dec(v_unused_1733_);
v___x_1671_ = v___x_1661_;
v_isShared_1672_ = v_isSharedCheck_1732_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_snapshotTasks_1669_);
lean_inc(v_infoState_1668_);
lean_inc(v_messages_1667_);
lean_inc(v_traceState_1666_);
lean_inc(v_auxDeclNGen_1665_);
lean_inc(v_ngen_1664_);
lean_inc(v_nextMacroScope_1663_);
lean_inc(v_env_1662_);
lean_dec(v___x_1661_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1732_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
lean_inc(v___x_1416_);
v___x_1673_ = l_Lean_Meta_addToCompletionBlackList(v_env_1662_, v___x_1416_);
v___x_1674_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 5, v___x_1674_);
lean_ctor_set(v___x_1671_, 0, v___x_1673_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_nextMacroScope_1663_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v_ngen_1664_);
lean_ctor_set(v_reuseFailAlloc_1731_, 3, v_auxDeclNGen_1665_);
lean_ctor_set(v_reuseFailAlloc_1731_, 4, v_traceState_1666_);
lean_ctor_set(v_reuseFailAlloc_1731_, 5, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1731_, 6, v_messages_1667_);
lean_ctor_set(v_reuseFailAlloc_1731_, 7, v_infoState_1668_);
lean_ctor_set(v_reuseFailAlloc_1731_, 8, v_snapshotTasks_1669_);
v___x_1676_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_mctx_1679_; lean_object* v_zetaDeltaFVarIds_1680_; lean_object* v_postponed_1681_; lean_object* v_diag_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1729_; 
v___x_1677_ = lean_st_ref_set(v___y_1422_, v___x_1676_);
v___x_1678_ = lean_st_ref_take(v___y_1420_);
v_mctx_1679_ = lean_ctor_get(v___x_1678_, 0);
v_zetaDeltaFVarIds_1680_ = lean_ctor_get(v___x_1678_, 2);
v_postponed_1681_ = lean_ctor_get(v___x_1678_, 3);
v_diag_1682_ = lean_ctor_get(v___x_1678_, 4);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1729_ == 0)
{
lean_object* v_unused_1730_; 
v_unused_1730_ = lean_ctor_get(v___x_1678_, 1);
lean_dec(v_unused_1730_);
v___x_1684_ = v___x_1678_;
v_isShared_1685_ = v_isSharedCheck_1729_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_diag_1682_);
lean_inc(v_postponed_1681_);
lean_inc(v_zetaDeltaFVarIds_1680_);
lean_inc(v_mctx_1679_);
lean_dec(v___x_1678_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1729_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_mctx_1679_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_zetaDeltaFVarIds_1680_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v_postponed_1681_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v_diag_1682_);
v___x_1688_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v_env_1691_; lean_object* v_nextMacroScope_1692_; lean_object* v_ngen_1693_; lean_object* v_auxDeclNGen_1694_; lean_object* v_traceState_1695_; lean_object* v_messages_1696_; lean_object* v_infoState_1697_; lean_object* v_snapshotTasks_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1726_; 
v___x_1689_ = lean_st_ref_set(v___y_1420_, v___x_1688_);
v___x_1690_ = lean_st_ref_take(v___y_1422_);
v_env_1691_ = lean_ctor_get(v___x_1690_, 0);
v_nextMacroScope_1692_ = lean_ctor_get(v___x_1690_, 1);
v_ngen_1693_ = lean_ctor_get(v___x_1690_, 2);
v_auxDeclNGen_1694_ = lean_ctor_get(v___x_1690_, 3);
v_traceState_1695_ = lean_ctor_get(v___x_1690_, 4);
v_messages_1696_ = lean_ctor_get(v___x_1690_, 6);
v_infoState_1697_ = lean_ctor_get(v___x_1690_, 7);
v_snapshotTasks_1698_ = lean_ctor_get(v___x_1690_, 8);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v___x_1690_, 5);
lean_dec(v_unused_1727_);
v___x_1700_ = v___x_1690_;
v_isShared_1701_ = v_isSharedCheck_1726_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snapshotTasks_1698_);
lean_inc(v_infoState_1697_);
lean_inc(v_messages_1696_);
lean_inc(v_traceState_1695_);
lean_inc(v_auxDeclNGen_1694_);
lean_inc(v_ngen_1693_);
lean_inc(v_nextMacroScope_1692_);
lean_inc(v_env_1691_);
lean_dec(v___x_1690_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1726_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1704_; 
lean_inc(v___x_1416_);
v___x_1702_ = l_Lean_addProtected(v_env_1691_, v___x_1416_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 5, v___x_1674_);
lean_ctor_set(v___x_1700_, 0, v___x_1702_);
v___x_1704_ = v___x_1700_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_nextMacroScope_1692_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_ngen_1693_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_auxDeclNGen_1694_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_traceState_1695_);
lean_ctor_set(v_reuseFailAlloc_1725_, 5, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1725_, 6, v_messages_1696_);
lean_ctor_set(v_reuseFailAlloc_1725_, 7, v_infoState_1697_);
lean_ctor_set(v_reuseFailAlloc_1725_, 8, v_snapshotTasks_1698_);
v___x_1704_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v_mctx_1707_; lean_object* v_zetaDeltaFVarIds_1708_; lean_object* v_postponed_1709_; lean_object* v_diag_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1723_; 
v___x_1705_ = lean_st_ref_set(v___y_1422_, v___x_1704_);
v___x_1706_ = lean_st_ref_take(v___y_1420_);
v_mctx_1707_ = lean_ctor_get(v___x_1706_, 0);
v_zetaDeltaFVarIds_1708_ = lean_ctor_get(v___x_1706_, 2);
v_postponed_1709_ = lean_ctor_get(v___x_1706_, 3);
v_diag_1710_ = lean_ctor_get(v___x_1706_, 4);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v___x_1706_, 1);
lean_dec(v_unused_1724_);
v___x_1712_ = v___x_1706_;
v_isShared_1713_ = v_isSharedCheck_1723_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_diag_1710_);
lean_inc(v_postponed_1709_);
lean_inc(v_zetaDeltaFVarIds_1708_);
lean_inc(v_mctx_1707_);
lean_dec(v___x_1706_);
v___x_1712_ = lean_box(0);
v_isShared_1713_ = v_isSharedCheck_1723_;
goto v_resetjp_1711_;
}
v_resetjp_1711_:
{
lean_object* v___x_1715_; 
if (v_isShared_1713_ == 0)
{
lean_ctor_set(v___x_1712_, 1, v___x_1686_);
v___x_1715_ = v___x_1712_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_mctx_1707_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_zetaDeltaFVarIds_1708_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_postponed_1709_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_diag_1710_);
v___x_1715_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v___x_1716_ = lean_st_ref_set(v___y_1420_, v___x_1715_);
v___x_1717_ = lean_unsigned_to_nat(1u);
v___x_1718_ = l_Lean_InductiveVal_numCtors(v_val_1409_);
lean_dec_ref(v_val_1409_);
v___x_1719_ = lean_nat_dec_eq(v___x_1718_, v___x_1717_);
lean_dec(v___x_1718_);
if (v___x_1719_ == 0)
{
v___y_1618_ = v___y_1419_;
v___y_1619_ = v___y_1420_;
v___y_1620_ = v___y_1421_;
v___y_1621_ = v___y_1422_;
goto v___jp_1617_;
}
else
{
uint8_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = 2;
lean_inc(v___x_1416_);
v___x_1721_ = l_Lean_Meta_setInlineAttribute(v___x_1416_, v___x_1720_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_dec_ref(v___x_1721_);
v___y_1618_ = v___y_1419_;
v___y_1619_ = v___y_1420_;
v___y_1620_ = v___y_1421_;
v___y_1621_ = v___y_1422_;
goto v___jp_1617_;
}
else
{
lean_dec_ref(v___x_1539_);
lean_dec(v_a_1519_);
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1411_);
return v___x_1721_;
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
lean_dec_ref(v___x_1539_);
lean_dec(v_a_1519_);
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1411_);
lean_dec_ref(v_val_1409_);
return v___x_1660_;
}
v___jp_1540_:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_compileDecl(v___x_1539_, v___x_1408_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v___x_1546_; 
lean_dec_ref(v___x_1545_);
lean_inc(v___x_1416_);
v___x_1546_ = l_Lean_enableRealizationsForConst(v___x_1416_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v___x_1547_; 
lean_dec_ref(v___x_1546_);
lean_inc(v_indName_1418_);
v___x_1547_ = l_Lean_isEnumType___at___00mkCtorIdx_spec__9(v_indName_1418_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1608_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1608_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1608_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_unbox(v_a_1548_);
lean_dec(v_a_1548_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_dec(v_a_1519_);
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1411_);
v___x_1553_ = lean_box(0);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1553_);
v___x_1555_ = v___x_1550_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1607_; 
lean_del_object(v___x_1550_);
lean_inc(v_indName_1418_);
v___x_1557_ = l_mkToCtorIdxName(v_indName_1418_);
lean_inc(v___x_1416_);
v___x_1558_ = l_Lean_mkConst(v___x_1416_, v___x_1411_);
v___x_1559_ = lean_box(1);
lean_inc(v___x_1557_);
v___x_1560_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkCtorIdx_spec__8___redArg(v___x_1557_, v_levelParams_1417_, v_a_1519_, v___x_1558_, v___x_1559_, v___y_1544_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
v_isSharedCheck_1607_ = !lean_is_exclusive(v___x_1560_);
if (v_isSharedCheck_1607_ == 0)
{
v___x_1563_ = v___x_1560_;
v_isShared_1564_ = v_isSharedCheck_1607_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1560_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1607_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 1);
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1606_; 
v_reuseFailAlloc_1606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1606_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1606_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_addDecl(v___x_1566_, v___x_1407_, v___y_1543_, v___y_1544_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1568_; lean_object* v_env_1569_; uint8_t v___x_1570_; 
lean_dec_ref(v___x_1567_);
v___x_1568_ = lean_st_ref_get(v___y_1544_);
v_env_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_ref(v_env_1569_);
lean_dec(v___x_1568_);
v___x_1570_ = l_Lean_isMarkedMeta(v_env_1569_, v_indName_1418_);
if (v___x_1570_ == 0)
{
v___y_1425_ = v___x_1557_;
v___y_1426_ = v___y_1541_;
v___y_1427_ = v___y_1542_;
v___y_1428_ = v___y_1543_;
v___y_1429_ = v___y_1544_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1571_; lean_object* v_env_1572_; lean_object* v_nextMacroScope_1573_; lean_object* v_ngen_1574_; lean_object* v_auxDeclNGen_1575_; lean_object* v_traceState_1576_; lean_object* v_messages_1577_; lean_object* v_infoState_1578_; lean_object* v_snapshotTasks_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1604_; 
v___x_1571_ = lean_st_ref_take(v___y_1544_);
v_env_1572_ = lean_ctor_get(v___x_1571_, 0);
v_nextMacroScope_1573_ = lean_ctor_get(v___x_1571_, 1);
v_ngen_1574_ = lean_ctor_get(v___x_1571_, 2);
v_auxDeclNGen_1575_ = lean_ctor_get(v___x_1571_, 3);
v_traceState_1576_ = lean_ctor_get(v___x_1571_, 4);
v_messages_1577_ = lean_ctor_get(v___x_1571_, 6);
v_infoState_1578_ = lean_ctor_get(v___x_1571_, 7);
v_snapshotTasks_1579_ = lean_ctor_get(v___x_1571_, 8);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v___x_1571_, 5);
lean_dec(v_unused_1605_);
v___x_1581_ = v___x_1571_;
v_isShared_1582_ = v_isSharedCheck_1604_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_snapshotTasks_1579_);
lean_inc(v_infoState_1578_);
lean_inc(v_messages_1577_);
lean_inc(v_traceState_1576_);
lean_inc(v_auxDeclNGen_1575_);
lean_inc(v_ngen_1574_);
lean_inc(v_nextMacroScope_1573_);
lean_inc(v_env_1572_);
lean_dec(v___x_1571_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1604_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
lean_inc(v___x_1557_);
v___x_1583_ = l_Lean_markMeta(v_env_1572_, v___x_1557_);
v___x_1584_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 5, v___x_1584_);
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1586_ = v___x_1581_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_nextMacroScope_1573_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_ngen_1574_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_auxDeclNGen_1575_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_traceState_1576_);
lean_ctor_set(v_reuseFailAlloc_1603_, 5, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1603_, 6, v_messages_1577_);
lean_ctor_set(v_reuseFailAlloc_1603_, 7, v_infoState_1578_);
lean_ctor_set(v_reuseFailAlloc_1603_, 8, v_snapshotTasks_1579_);
v___x_1586_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_mctx_1589_; lean_object* v_zetaDeltaFVarIds_1590_; lean_object* v_postponed_1591_; lean_object* v_diag_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1601_; 
v___x_1587_ = lean_st_ref_set(v___y_1544_, v___x_1586_);
v___x_1588_ = lean_st_ref_take(v___y_1542_);
v_mctx_1589_ = lean_ctor_get(v___x_1588_, 0);
v_zetaDeltaFVarIds_1590_ = lean_ctor_get(v___x_1588_, 2);
v_postponed_1591_ = lean_ctor_get(v___x_1588_, 3);
v_diag_1592_ = lean_ctor_get(v___x_1588_, 4);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1588_, 1);
lean_dec(v_unused_1602_);
v___x_1594_ = v___x_1588_;
v_isShared_1595_ = v_isSharedCheck_1601_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_diag_1592_);
lean_inc(v_postponed_1591_);
lean_inc(v_zetaDeltaFVarIds_1590_);
lean_inc(v_mctx_1589_);
lean_dec(v___x_1588_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1601_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1596_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 1, v___x_1596_);
v___x_1598_ = v___x_1594_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_mctx_1589_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_zetaDeltaFVarIds_1590_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_postponed_1591_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_diag_1592_);
v___x_1598_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_st_ref_set(v___y_1542_, v___x_1598_);
v___y_1425_ = v___x_1557_;
v___y_1426_ = v___y_1541_;
v___y_1427_ = v___y_1542_;
v___y_1428_ = v___y_1543_;
v___y_1429_ = v___y_1544_;
goto v___jp_1424_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1557_);
lean_dec(v_indName_1418_);
lean_dec(v___x_1416_);
return v___x_1567_;
}
}
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
lean_dec(v_a_1519_);
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1411_);
v_a_1609_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1547_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1547_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
else
{
lean_dec(v_a_1519_);
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1411_);
return v___x_1546_;
}
}
else
{
lean_dec(v_a_1519_);
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1411_);
return v___x_1545_;
}
}
v___jp_1617_:
{
lean_object* v___x_1622_; lean_object* v_env_1623_; uint8_t v___x_1624_; 
v___x_1622_ = lean_st_ref_get(v___y_1621_);
v_env_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref(v_env_1623_);
lean_dec(v___x_1622_);
lean_inc(v_indName_1418_);
v___x_1624_ = l_Lean_isMarkedMeta(v_env_1623_, v_indName_1418_);
if (v___x_1624_ == 0)
{
v___y_1541_ = v___y_1618_;
v___y_1542_ = v___y_1619_;
v___y_1543_ = v___y_1620_;
v___y_1544_ = v___y_1621_;
goto v___jp_1540_;
}
else
{
lean_object* v___x_1625_; lean_object* v_env_1626_; lean_object* v_nextMacroScope_1627_; lean_object* v_ngen_1628_; lean_object* v_auxDeclNGen_1629_; lean_object* v_traceState_1630_; lean_object* v_messages_1631_; lean_object* v_infoState_1632_; lean_object* v_snapshotTasks_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1658_; 
v___x_1625_ = lean_st_ref_take(v___y_1621_);
v_env_1626_ = lean_ctor_get(v___x_1625_, 0);
v_nextMacroScope_1627_ = lean_ctor_get(v___x_1625_, 1);
v_ngen_1628_ = lean_ctor_get(v___x_1625_, 2);
v_auxDeclNGen_1629_ = lean_ctor_get(v___x_1625_, 3);
v_traceState_1630_ = lean_ctor_get(v___x_1625_, 4);
v_messages_1631_ = lean_ctor_get(v___x_1625_, 6);
v_infoState_1632_ = lean_ctor_get(v___x_1625_, 7);
v_snapshotTasks_1633_ = lean_ctor_get(v___x_1625_, 8);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1658_ == 0)
{
lean_object* v_unused_1659_; 
v_unused_1659_ = lean_ctor_get(v___x_1625_, 5);
lean_dec(v_unused_1659_);
v___x_1635_ = v___x_1625_;
v_isShared_1636_ = v_isSharedCheck_1658_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_snapshotTasks_1633_);
lean_inc(v_infoState_1632_);
lean_inc(v_messages_1631_);
lean_inc(v_traceState_1630_);
lean_inc(v_auxDeclNGen_1629_);
lean_inc(v_ngen_1628_);
lean_inc(v_nextMacroScope_1627_);
lean_inc(v_env_1626_);
lean_dec(v___x_1625_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1658_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1640_; 
lean_inc(v___x_1416_);
v___x_1637_ = l_Lean_markMeta(v_env_1626_, v___x_1416_);
v___x_1638_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 5, v___x_1638_);
lean_ctor_set(v___x_1635_, 0, v___x_1637_);
v___x_1640_ = v___x_1635_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v___x_1637_);
lean_ctor_set(v_reuseFailAlloc_1657_, 1, v_nextMacroScope_1627_);
lean_ctor_set(v_reuseFailAlloc_1657_, 2, v_ngen_1628_);
lean_ctor_set(v_reuseFailAlloc_1657_, 3, v_auxDeclNGen_1629_);
lean_ctor_set(v_reuseFailAlloc_1657_, 4, v_traceState_1630_);
lean_ctor_set(v_reuseFailAlloc_1657_, 5, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1657_, 6, v_messages_1631_);
lean_ctor_set(v_reuseFailAlloc_1657_, 7, v_infoState_1632_);
lean_ctor_set(v_reuseFailAlloc_1657_, 8, v_snapshotTasks_1633_);
v___x_1640_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_mctx_1643_; lean_object* v_zetaDeltaFVarIds_1644_; lean_object* v_postponed_1645_; lean_object* v_diag_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1655_; 
v___x_1641_ = lean_st_ref_set(v___y_1621_, v___x_1640_);
v___x_1642_ = lean_st_ref_take(v___y_1619_);
v_mctx_1643_ = lean_ctor_get(v___x_1642_, 0);
v_zetaDeltaFVarIds_1644_ = lean_ctor_get(v___x_1642_, 2);
v_postponed_1645_ = lean_ctor_get(v___x_1642_, 3);
v_diag_1646_ = lean_ctor_get(v___x_1642_, 4);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1655_ == 0)
{
lean_object* v_unused_1656_; 
v_unused_1656_ = lean_ctor_get(v___x_1642_, 1);
lean_dec(v_unused_1656_);
v___x_1648_ = v___x_1642_;
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_diag_1646_);
lean_inc(v_postponed_1645_);
lean_inc(v_zetaDeltaFVarIds_1644_);
lean_inc(v_mctx_1643_);
lean_dec(v___x_1642_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1655_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 1, v___x_1650_);
v___x_1652_ = v___x_1648_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_mctx_1643_);
lean_ctor_set(v_reuseFailAlloc_1654_, 1, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1654_, 2, v_zetaDeltaFVarIds_1644_);
lean_ctor_set(v_reuseFailAlloc_1654_, 3, v_postponed_1645_);
lean_ctor_set(v_reuseFailAlloc_1654_, 4, v_diag_1646_);
v___x_1652_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
lean_object* v___x_1653_; 
v___x_1653_ = lean_st_ref_set(v___y_1619_, v___x_1652_);
v___y_1541_ = v___y_1618_;
v___y_1542_ = v___y_1619_;
v___y_1543_ = v___y_1620_;
v___y_1544_ = v___y_1621_;
goto v___jp_1540_;
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
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
lean_dec(v_a_1519_);
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1411_);
lean_dec_ref(v_val_1409_);
v_a_1736_ = lean_ctor_get(v___x_1525_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1525_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1525_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1525_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1751_; 
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1415_);
lean_dec(v_ctors_1414_);
lean_dec_ref(v___x_1413_);
lean_dec(v___x_1412_);
lean_dec(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v_val_1409_);
lean_dec_ref(v_xs_1406_);
lean_dec_ref(v___x_1405_);
lean_dec_ref(v___x_1404_);
v_a_1744_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1751_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1746_ = v___x_1518_;
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_dec(v___x_1518_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1751_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v___x_1749_; 
if (v_isShared_1747_ == 0)
{
v___x_1749_ = v___x_1746_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
else
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1759_; 
lean_dec(v_indName_1418_);
lean_dec(v_levelParams_1417_);
lean_dec(v___x_1416_);
lean_dec(v___x_1415_);
lean_dec(v_ctors_1414_);
lean_dec_ref(v___x_1413_);
lean_dec(v___x_1412_);
lean_dec(v___x_1411_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v_val_1409_);
lean_dec_ref(v_xs_1406_);
lean_dec_ref(v___x_1405_);
lean_dec_ref(v___x_1404_);
v_a_1752_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1759_ == 0)
{
v___x_1754_ = v___x_1515_;
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1515_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1759_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_a_1752_);
v___x_1757_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
return v___x_1757_;
}
}
}
v___jp_1424_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1430_ = lean_unsigned_to_nat(1u);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1430_);
lean_inc(v___y_1425_);
v___x_1432_ = lean_array_push(v___x_1431_, v___y_1425_);
v___x_1433_ = l_Lean_compileDecls(v___x_1432_, v___x_1408_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1433_) == 0)
{
lean_object* v___x_1434_; lean_object* v_env_1435_; lean_object* v_nextMacroScope_1436_; lean_object* v_ngen_1437_; lean_object* v_auxDeclNGen_1438_; lean_object* v_traceState_1439_; lean_object* v_messages_1440_; lean_object* v_infoState_1441_; lean_object* v_snapshotTasks_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1513_; 
lean_dec_ref(v___x_1433_);
v___x_1434_ = lean_st_ref_take(v___y_1429_);
v_env_1435_ = lean_ctor_get(v___x_1434_, 0);
v_nextMacroScope_1436_ = lean_ctor_get(v___x_1434_, 1);
v_ngen_1437_ = lean_ctor_get(v___x_1434_, 2);
v_auxDeclNGen_1438_ = lean_ctor_get(v___x_1434_, 3);
v_traceState_1439_ = lean_ctor_get(v___x_1434_, 4);
v_messages_1440_ = lean_ctor_get(v___x_1434_, 6);
v_infoState_1441_ = lean_ctor_get(v___x_1434_, 7);
v_snapshotTasks_1442_ = lean_ctor_get(v___x_1434_, 8);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v___x_1434_, 5);
lean_dec(v_unused_1514_);
v___x_1444_ = v___x_1434_;
v_isShared_1445_ = v_isSharedCheck_1513_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_snapshotTasks_1442_);
lean_inc(v_infoState_1441_);
lean_inc(v_messages_1440_);
lean_inc(v_traceState_1439_);
lean_inc(v_auxDeclNGen_1438_);
lean_inc(v_ngen_1437_);
lean_inc(v_nextMacroScope_1436_);
lean_inc(v_env_1435_);
lean_dec(v___x_1434_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1513_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
lean_inc(v___y_1425_);
v___x_1446_ = l_Lean_Meta_addToCompletionBlackList(v_env_1435_, v___y_1425_);
v___x_1447_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 5, v___x_1447_);
lean_ctor_set(v___x_1444_, 0, v___x_1446_);
v___x_1449_ = v___x_1444_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_nextMacroScope_1436_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_ngen_1437_);
lean_ctor_set(v_reuseFailAlloc_1512_, 3, v_auxDeclNGen_1438_);
lean_ctor_set(v_reuseFailAlloc_1512_, 4, v_traceState_1439_);
lean_ctor_set(v_reuseFailAlloc_1512_, 5, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1512_, 6, v_messages_1440_);
lean_ctor_set(v_reuseFailAlloc_1512_, 7, v_infoState_1441_);
lean_ctor_set(v_reuseFailAlloc_1512_, 8, v_snapshotTasks_1442_);
v___x_1449_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v_mctx_1452_; lean_object* v_zetaDeltaFVarIds_1453_; lean_object* v_postponed_1454_; lean_object* v_diag_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1510_; 
v___x_1450_ = lean_st_ref_set(v___y_1429_, v___x_1449_);
v___x_1451_ = lean_st_ref_take(v___y_1427_);
v_mctx_1452_ = lean_ctor_get(v___x_1451_, 0);
v_zetaDeltaFVarIds_1453_ = lean_ctor_get(v___x_1451_, 2);
v_postponed_1454_ = lean_ctor_get(v___x_1451_, 3);
v_diag_1455_ = lean_ctor_get(v___x_1451_, 4);
v_isSharedCheck_1510_ = !lean_is_exclusive(v___x_1451_);
if (v_isSharedCheck_1510_ == 0)
{
lean_object* v_unused_1511_; 
v_unused_1511_ = lean_ctor_get(v___x_1451_, 1);
lean_dec(v_unused_1511_);
v___x_1457_ = v___x_1451_;
v_isShared_1458_ = v_isSharedCheck_1510_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_diag_1455_);
lean_inc(v_postponed_1454_);
lean_inc(v_zetaDeltaFVarIds_1453_);
lean_inc(v_mctx_1452_);
lean_dec(v___x_1451_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1510_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1459_ = lean_obj_once(&l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v___x_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_mctx_1452_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_zetaDeltaFVarIds_1453_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_postponed_1454_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_diag_1455_);
v___x_1461_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_env_1464_; lean_object* v_nextMacroScope_1465_; lean_object* v_ngen_1466_; lean_object* v_auxDeclNGen_1467_; lean_object* v_traceState_1468_; lean_object* v_messages_1469_; lean_object* v_infoState_1470_; lean_object* v_snapshotTasks_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1507_; 
v___x_1462_ = lean_st_ref_set(v___y_1427_, v___x_1461_);
v___x_1463_ = lean_st_ref_take(v___y_1429_);
v_env_1464_ = lean_ctor_get(v___x_1463_, 0);
v_nextMacroScope_1465_ = lean_ctor_get(v___x_1463_, 1);
v_ngen_1466_ = lean_ctor_get(v___x_1463_, 2);
v_auxDeclNGen_1467_ = lean_ctor_get(v___x_1463_, 3);
v_traceState_1468_ = lean_ctor_get(v___x_1463_, 4);
v_messages_1469_ = lean_ctor_get(v___x_1463_, 6);
v_infoState_1470_ = lean_ctor_get(v___x_1463_, 7);
v_snapshotTasks_1471_ = lean_ctor_get(v___x_1463_, 8);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v___x_1463_, 5);
lean_dec(v_unused_1508_);
v___x_1473_ = v___x_1463_;
v_isShared_1474_ = v_isSharedCheck_1507_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snapshotTasks_1471_);
lean_inc(v_infoState_1470_);
lean_inc(v_messages_1469_);
lean_inc(v_traceState_1468_);
lean_inc(v_auxDeclNGen_1467_);
lean_inc(v_ngen_1466_);
lean_inc(v_nextMacroScope_1465_);
lean_inc(v_env_1464_);
lean_dec(v___x_1463_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1507_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_inc(v___y_1425_);
v___x_1475_ = l_Lean_addProtected(v_env_1464_, v___y_1425_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 5, v___x_1447_);
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1506_, 1, v_nextMacroScope_1465_);
lean_ctor_set(v_reuseFailAlloc_1506_, 2, v_ngen_1466_);
lean_ctor_set(v_reuseFailAlloc_1506_, 3, v_auxDeclNGen_1467_);
lean_ctor_set(v_reuseFailAlloc_1506_, 4, v_traceState_1468_);
lean_ctor_set(v_reuseFailAlloc_1506_, 5, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1506_, 6, v_messages_1469_);
lean_ctor_set(v_reuseFailAlloc_1506_, 7, v_infoState_1470_);
lean_ctor_set(v_reuseFailAlloc_1506_, 8, v_snapshotTasks_1471_);
v___x_1477_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v_mctx_1480_; lean_object* v_zetaDeltaFVarIds_1481_; lean_object* v_postponed_1482_; lean_object* v_diag_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1504_; 
v___x_1478_ = lean_st_ref_set(v___y_1429_, v___x_1477_);
v___x_1479_ = lean_st_ref_take(v___y_1427_);
v_mctx_1480_ = lean_ctor_get(v___x_1479_, 0);
v_zetaDeltaFVarIds_1481_ = lean_ctor_get(v___x_1479_, 2);
v_postponed_1482_ = lean_ctor_get(v___x_1479_, 3);
v_diag_1483_ = lean_ctor_get(v___x_1479_, 4);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1504_ == 0)
{
lean_object* v_unused_1505_; 
v_unused_1505_ = lean_ctor_get(v___x_1479_, 1);
lean_dec(v_unused_1505_);
v___x_1485_ = v___x_1479_;
v_isShared_1486_ = v_isSharedCheck_1504_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_diag_1483_);
lean_inc(v_postponed_1482_);
lean_inc(v_zetaDeltaFVarIds_1481_);
lean_inc(v_mctx_1480_);
lean_dec(v___x_1479_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1504_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1459_);
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_mctx_1480_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_zetaDeltaFVarIds_1481_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_postponed_1482_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_diag_1483_);
v___x_1488_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1501_; 
v___x_1489_ = lean_st_ref_set(v___y_1427_, v___x_1488_);
lean_inc(v___y_1425_);
v___x_1490_ = l_Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10(v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
v_isSharedCheck_1501_ = !lean_is_exclusive(v___x_1490_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v___x_1490_, 0);
lean_dec(v_unused_1502_);
v___x_1492_ = v___x_1490_;
v_isShared_1493_ = v_isSharedCheck_1501_;
goto v_resetjp_1491_;
}
else
{
lean_dec(v___x_1490_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1501_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 1);
lean_ctor_set(v___x_1492_, 0, v___x_1416_);
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1416_);
v___x_1495_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1496_ = lean_box(0);
v___x_1497_ = ((lean_object*)(l_mkCtorIdx___lam__1___closed__1));
v___x_1498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1495_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
lean_ctor_set(v___x_1498_, 2, v___x_1497_);
v___x_1499_ = l_Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11(v___y_1425_, v___x_1498_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
return v___x_1499_;
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
lean_dec(v___y_1425_);
lean_dec(v___x_1416_);
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1760_ = _args[0];
lean_object* v___x_1761_ = _args[1];
lean_object* v_xs_1762_ = _args[2];
lean_object* v___x_1763_ = _args[3];
lean_object* v___x_1764_ = _args[4];
lean_object* v_val_1765_ = _args[5];
lean_object* v___x_1766_ = _args[6];
lean_object* v___x_1767_ = _args[7];
lean_object* v___x_1768_ = _args[8];
lean_object* v___x_1769_ = _args[9];
lean_object* v_ctors_1770_ = _args[10];
lean_object* v___x_1771_ = _args[11];
lean_object* v___x_1772_ = _args[12];
lean_object* v_levelParams_1773_ = _args[13];
lean_object* v_indName_1774_ = _args[14];
lean_object* v___y_1775_ = _args[15];
lean_object* v___y_1776_ = _args[16];
lean_object* v___y_1777_ = _args[17];
lean_object* v___y_1778_ = _args[18];
lean_object* v___y_1779_ = _args[19];
_start:
{
uint8_t v___x_36063__boxed_1780_; uint8_t v___x_36064__boxed_1781_; lean_object* v_res_1782_; 
v___x_36063__boxed_1780_ = lean_unbox(v___x_1763_);
v___x_36064__boxed_1781_ = lean_unbox(v___x_1764_);
v_res_1782_ = l_mkCtorIdx___lam__1(v___x_1760_, v___x_1761_, v_xs_1762_, v___x_36063__boxed_1780_, v___x_36064__boxed_1781_, v_val_1765_, v___x_1766_, v___x_1767_, v___x_1768_, v___x_1769_, v_ctors_1770_, v___x_1771_, v___x_1772_, v_levelParams_1773_, v_indName_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
lean_dec(v___y_1778_);
lean_dec_ref(v___y_1777_);
lean_dec(v___y_1776_);
lean_dec_ref(v___y_1775_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(lean_object* v_bs_1783_, lean_object* v_k_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1783_, v_k_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1790_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
else
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
v_a_1799_ = lean_ctor_get(v___x_1790_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1790_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1790_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object* v_bs_1807_, lean_object* v_k_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_1807_, v_k_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec_ref(v_bs_1807_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(size_t v_sz_1815_, size_t v_i_1816_, lean_object* v_bs_1817_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = lean_usize_dec_lt(v_i_1816_, v_sz_1815_);
if (v___x_1818_ == 0)
{
return v_bs_1817_;
}
else
{
lean_object* v_v_1819_; lean_object* v___x_1820_; lean_object* v_bs_x27_1821_; lean_object* v___x_1822_; uint8_t v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v_v_1819_ = lean_array_uget(v_bs_1817_, v_i_1816_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v_bs_x27_1821_ = lean_array_uset(v_bs_1817_, v_i_1816_, v___x_1820_);
v___x_1822_ = l_Lean_Expr_fvarId_x21(v_v_1819_);
lean_dec(v_v_1819_);
v___x_1823_ = 1;
v___x_1824_ = lean_box(v___x_1823_);
v___x_1825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1822_);
lean_ctor_set(v___x_1825_, 1, v___x_1824_);
v___x_1826_ = ((size_t)1ULL);
v___x_1827_ = lean_usize_add(v_i_1816_, v___x_1826_);
v___x_1828_ = lean_array_uset(v_bs_x27_1821_, v_i_1816_, v___x_1825_);
v_i_1816_ = v___x_1827_;
v_bs_1817_ = v___x_1828_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19___boxed(lean_object* v_sz_1830_, lean_object* v_i_1831_, lean_object* v_bs_1832_){
_start:
{
size_t v_sz_boxed_1833_; size_t v_i_boxed_1834_; lean_object* v_res_1835_; 
v_sz_boxed_1833_ = lean_unbox_usize(v_sz_1830_);
lean_dec(v_sz_1830_);
v_i_boxed_1834_ = lean_unbox_usize(v_i_1831_);
lean_dec(v_i_1831_);
v_res_1835_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_boxed_1833_, v_i_boxed_1834_, v_bs_1832_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(lean_object* v_bs_1836_, lean_object* v_k_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
size_t v_sz_1843_; size_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v_sz_1843_ = lean_array_size(v_bs_1836_);
v___x_1844_ = ((size_t)0ULL);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__19(v_sz_1843_, v___x_1844_, v_bs_1836_);
v___x_1846_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v___x_1845_, v_k_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
lean_dec_ref(v___x_1845_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg___boxed(lean_object* v_bs_1847_, lean_object* v_k_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_1847_, v_k_1848_, v___y_1849_, v___y_1850_, v___y_1851_, v___y_1852_);
lean_dec(v___y_1852_);
lean_dec_ref(v___y_1851_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2(lean_object* v_numParams_1858_, lean_object* v_indName_1859_, lean_object* v___x_1860_, lean_object* v___x_1861_, uint8_t v___x_1862_, uint8_t v___x_1863_, lean_object* v_val_1864_, lean_object* v___x_1865_, lean_object* v_ctors_1866_, lean_object* v___x_1867_, lean_object* v_levelParams_1868_, lean_object* v_xs_1869_, lean_object* v_x_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___f_1888_; lean_object* v___x_1889_; 
v___x_1876_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1858_);
lean_inc_ref_n(v_xs_1869_, 3);
v___x_1877_ = l_Array_toSubarray___redArg(v_xs_1869_, v___x_1876_, v_numParams_1858_);
v___x_1878_ = l_Subarray_copy___redArg(v___x_1877_);
v___x_1879_ = lean_array_get_size(v_xs_1869_);
v___x_1880_ = l_Array_toSubarray___redArg(v_xs_1869_, v_numParams_1858_, v___x_1879_);
v___x_1881_ = l_Subarray_copy___redArg(v___x_1880_);
lean_inc(v___x_1860_);
lean_inc(v_indName_1859_);
v___x_1882_ = l_Lean_mkConst(v_indName_1859_, v___x_1860_);
v___x_1883_ = l_Lean_mkAppN(v___x_1882_, v_xs_1869_);
v___x_1884_ = ((lean_object*)(l_mkCtorIdx___lam__2___closed__1));
v___x_1885_ = l_Lean_mkConst(v___x_1884_, v___x_1861_);
v___x_1886_ = lean_box(v___x_1862_);
v___x_1887_ = lean_box(v___x_1863_);
v___f_1888_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1888_, 0, v___x_1883_);
lean_closure_set(v___f_1888_, 1, v___x_1885_);
lean_closure_set(v___f_1888_, 2, v_xs_1869_);
lean_closure_set(v___f_1888_, 3, v___x_1886_);
lean_closure_set(v___f_1888_, 4, v___x_1887_);
lean_closure_set(v___f_1888_, 5, v_val_1864_);
lean_closure_set(v___f_1888_, 6, v___x_1881_);
lean_closure_set(v___f_1888_, 7, v___x_1860_);
lean_closure_set(v___f_1888_, 8, v___x_1865_);
lean_closure_set(v___f_1888_, 9, v___x_1878_);
lean_closure_set(v___f_1888_, 10, v_ctors_1866_);
lean_closure_set(v___f_1888_, 11, v___x_1876_);
lean_closure_set(v___f_1888_, 12, v___x_1867_);
lean_closure_set(v___f_1888_, 13, v_levelParams_1868_);
lean_closure_set(v___f_1888_, 14, v_indName_1859_);
v___x_1889_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_xs_1869_, v___f_1888_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1890_ = _args[0];
lean_object* v_indName_1891_ = _args[1];
lean_object* v___x_1892_ = _args[2];
lean_object* v___x_1893_ = _args[3];
lean_object* v___x_1894_ = _args[4];
lean_object* v___x_1895_ = _args[5];
lean_object* v_val_1896_ = _args[6];
lean_object* v___x_1897_ = _args[7];
lean_object* v_ctors_1898_ = _args[8];
lean_object* v___x_1899_ = _args[9];
lean_object* v_levelParams_1900_ = _args[10];
lean_object* v_xs_1901_ = _args[11];
lean_object* v_x_1902_ = _args[12];
lean_object* v___y_1903_ = _args[13];
lean_object* v___y_1904_ = _args[14];
lean_object* v___y_1905_ = _args[15];
lean_object* v___y_1906_ = _args[16];
lean_object* v___y_1907_ = _args[17];
_start:
{
uint8_t v___x_36751__boxed_1908_; uint8_t v___x_36752__boxed_1909_; lean_object* v_res_1910_; 
v___x_36751__boxed_1908_ = lean_unbox(v___x_1894_);
v___x_36752__boxed_1909_ = lean_unbox(v___x_1895_);
v_res_1910_ = l_mkCtorIdx___lam__2(v_numParams_1890_, v_indName_1891_, v___x_1892_, v___x_1893_, v___x_36751__boxed_1908_, v___x_36752__boxed_1909_, v_val_1896_, v___x_1897_, v_ctors_1898_, v___x_1899_, v_levelParams_1900_, v_xs_1901_, v_x_1902_, v___y_1903_, v___y_1904_, v___y_1905_, v___y_1906_);
lean_dec(v___y_1906_);
lean_dec_ref(v___y_1905_);
lean_dec(v___y_1904_);
lean_dec_ref(v___y_1903_);
lean_dec_ref(v_x_1902_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00mkCtorIdx_spec__3(lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
if (lean_obj_tag(v_a_1911_) == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = l_List_reverse___redArg(v_a_1912_);
return v___x_1913_;
}
else
{
lean_object* v_head_1914_; lean_object* v_tail_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1924_; 
v_head_1914_ = lean_ctor_get(v_a_1911_, 0);
v_tail_1915_ = lean_ctor_get(v_a_1911_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_a_1911_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1917_ = v_a_1911_;
v_isShared_1918_ = v_isSharedCheck_1924_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_tail_1915_);
lean_inc(v_head_1914_);
lean_dec(v_a_1911_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1924_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = l_Lean_mkLevelParam(v_head_1914_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 1, v_a_1912_);
lean_ctor_set(v___x_1917_, 0, v___x_1919_);
v___x_1921_ = v___x_1917_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v___x_1919_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_a_1912_);
v___x_1921_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
v_a_1911_ = v_tail_1915_;
v_a_1912_ = v___x_1921_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1927_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4___closed__6));
v___x_1928_ = lean_unsigned_to_nat(62u);
v___x_1929_ = lean_unsigned_to_nat(48u);
v___x_1930_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__1));
v___x_1931_ = ((lean_object*)(l_mkCtorIdx___lam__3___closed__0));
v___x_1932_ = l_mkPanicMessageWithDecl(v___x_1931_, v___x_1930_, v___x_1929_, v___x_1928_, v___x_1927_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3(lean_object* v_indName_1933_, uint8_t v___x_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_){
_start:
{
lean_object* v_options_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v_options_1940_ = lean_ctor_get(v___y_1937_, 2);
v___x_1941_ = l___private_Lean_Meta_Constructions_CtorIdx_0__genCtorIdx;
v___x_1942_ = l_Lean_Option_get___at___00mkCtorIdx_spec__0(v_options_1940_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_indName_1933_);
v___x_1943_ = lean_box(0);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_2031_; 
lean_inc(v_indName_1933_);
v___x_1945_ = l_mkCtorIdxName(v_indName_1933_);
lean_inc(v___x_1945_);
v___x_1946_ = l_Lean_hasConst___at___00mkCtorIdx_spec__1___redArg(v___x_1945_, v___x_1942_, v___y_1938_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1949_ = v___x_1946_;
v_isShared_1950_ = v_isSharedCheck_2031_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1946_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_2031_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
uint8_t v___x_1951_; 
v___x_1951_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; 
lean_del_object(v___x_1949_);
lean_inc(v_indName_1933_);
v___x_1952_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v_indName_1933_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
if (lean_obj_tag(v_a_1953_) == 5)
{
lean_object* v_val_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2016_; 
v_val_1954_ = lean_ctor_get(v_a_1953_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v_a_1953_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_1956_ = v_a_1953_;
v_isShared_1957_ = v_isSharedCheck_2016_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_val_1954_);
lean_dec(v_a_1953_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2016_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v_toConstantVal_1958_; lean_object* v_numParams_1959_; lean_object* v_numIndices_1960_; lean_object* v_ctors_1961_; lean_object* v_levelParams_1962_; lean_object* v_type_1963_; lean_object* v___x_1964_; 
v_toConstantVal_1958_ = lean_ctor_get(v_val_1954_, 0);
v_numParams_1959_ = lean_ctor_get(v_val_1954_, 1);
lean_inc(v_numParams_1959_);
v_numIndices_1960_ = lean_ctor_get(v_val_1954_, 2);
lean_inc(v_numIndices_1960_);
v_ctors_1961_ = lean_ctor_get(v_val_1954_, 4);
lean_inc(v_ctors_1961_);
v_levelParams_1962_ = lean_ctor_get(v_toConstantVal_1958_, 1);
lean_inc(v_levelParams_1962_);
v_type_1963_ = lean_ctor_get(v_toConstantVal_1958_, 2);
lean_inc_ref_n(v_type_1963_, 2);
v___x_1964_ = l_Lean_Meta_isPropFormerType(v_type_1963_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2007_; 
v_a_1965_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1967_ = v___x_1964_;
v_isShared_1968_ = v_isSharedCheck_2007_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___x_1964_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2007_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_unbox(v_a_1965_);
lean_dec(v_a_1965_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_del_object(v___x_1967_);
lean_inc(v_indName_1933_);
v___x_1970_ = l_Lean_mkCasesOnName(v_indName_1933_);
lean_inc(v___x_1970_);
v___x_1971_ = l_Lean_getConstInfo___at___00mkCtorIdx_spec__2(v___x_1970_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1994_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1974_ = v___x_1971_;
v_isShared_1975_ = v_isSharedCheck_1994_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_a_1972_);
lean_dec(v___x_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1994_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v___x_1976_ = l_List_lengthTR___redArg(v_levelParams_1962_);
v___x_1977_ = l_Lean_ConstantInfo_levelParams(v_a_1972_);
lean_dec(v_a_1972_);
v___x_1978_ = l_List_lengthTR___redArg(v___x_1977_);
lean_dec(v___x_1977_);
v___x_1979_ = lean_nat_dec_lt(v___x_1976_, v___x_1978_);
lean_dec(v___x_1978_);
lean_dec(v___x_1976_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
lean_dec(v___x_1970_);
lean_dec_ref(v_type_1963_);
lean_dec(v_levelParams_1962_);
lean_dec(v_ctors_1961_);
lean_dec(v_numIndices_1960_);
lean_dec(v_numParams_1959_);
lean_del_object(v___x_1956_);
lean_dec_ref(v_val_1954_);
lean_dec(v___x_1945_);
lean_dec(v_indName_1933_);
v___x_1980_ = lean_box(0);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1980_);
v___x_1982_ = v___x_1974_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___f_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
lean_del_object(v___x_1974_);
v___x_1984_ = lean_box(0);
lean_inc(v_levelParams_1962_);
v___x_1985_ = l_List_mapTR_loop___at___00mkCtorIdx_spec__3(v_levelParams_1962_, v___x_1984_);
v___x_1986_ = lean_box(v___x_1934_);
v___x_1987_ = lean_box(v___x_1942_);
lean_inc(v_numParams_1959_);
v___f_1988_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_1988_, 0, v_numParams_1959_);
lean_closure_set(v___f_1988_, 1, v_indName_1933_);
lean_closure_set(v___f_1988_, 2, v___x_1985_);
lean_closure_set(v___f_1988_, 3, v___x_1984_);
lean_closure_set(v___f_1988_, 4, v___x_1986_);
lean_closure_set(v___f_1988_, 5, v___x_1987_);
lean_closure_set(v___f_1988_, 6, v_val_1954_);
lean_closure_set(v___f_1988_, 7, v___x_1970_);
lean_closure_set(v___f_1988_, 8, v_ctors_1961_);
lean_closure_set(v___f_1988_, 9, v___x_1945_);
lean_closure_set(v___f_1988_, 10, v_levelParams_1962_);
v___x_1989_ = lean_nat_add(v_numParams_1959_, v_numIndices_1960_);
lean_dec(v_numIndices_1960_);
lean_dec(v_numParams_1959_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set_tag(v___x_1956_, 1);
lean_ctor_set(v___x_1956_, 0, v___x_1989_);
v___x_1991_ = v___x_1956_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
lean_object* v___x_1992_; 
v___x_1992_ = l_Lean_Meta_forallBoundedTelescope___at___00mkCtorIdx_spec__5___redArg(v_type_1963_, v___x_1991_, v___f_1988_, v___x_1934_, v___x_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
return v___x_1992_;
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec(v___x_1970_);
lean_dec_ref(v_type_1963_);
lean_dec(v_levelParams_1962_);
lean_dec(v_ctors_1961_);
lean_dec(v_numIndices_1960_);
lean_dec(v_numParams_1959_);
lean_del_object(v___x_1956_);
lean_dec_ref(v_val_1954_);
lean_dec(v___x_1945_);
lean_dec(v_indName_1933_);
v_a_1995_ = lean_ctor_get(v___x_1971_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1971_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1971_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
else
{
lean_object* v___x_2003_; lean_object* v___x_2005_; 
lean_dec_ref(v_type_1963_);
lean_dec(v_levelParams_1962_);
lean_dec(v_ctors_1961_);
lean_dec(v_numIndices_1960_);
lean_dec(v_numParams_1959_);
lean_del_object(v___x_1956_);
lean_dec_ref(v_val_1954_);
lean_dec(v___x_1945_);
lean_dec(v_indName_1933_);
v___x_2003_ = lean_box(0);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_2003_);
v___x_2005_ = v___x_1967_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_type_1963_);
lean_dec(v_levelParams_1962_);
lean_dec(v_ctors_1961_);
lean_dec(v_numIndices_1960_);
lean_dec(v_numParams_1959_);
lean_del_object(v___x_1956_);
lean_dec_ref(v_val_1954_);
lean_dec(v___x_1945_);
lean_dec(v_indName_1933_);
v_a_2008_ = lean_ctor_get(v___x_1964_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1964_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1964_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
}
else
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec(v_a_1953_);
lean_dec(v___x_1945_);
lean_dec(v_indName_1933_);
v___x_2017_ = lean_obj_once(&l_mkCtorIdx___lam__3___closed__2, &l_mkCtorIdx___lam__3___closed__2_once, _init_l_mkCtorIdx___lam__3___closed__2);
v___x_2018_ = l_panic___at___00mkCtorIdx_spec__13(v___x_2017_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
return v___x_2018_;
}
}
else
{
lean_object* v_a_2019_; lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2026_; 
lean_dec(v___x_1945_);
lean_dec(v_indName_1933_);
v_a_2019_ = lean_ctor_get(v___x_1952_, 0);
v_isSharedCheck_2026_ = !lean_is_exclusive(v___x_1952_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2021_ = v___x_1952_;
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
else
{
lean_inc(v_a_2019_);
lean_dec(v___x_1952_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2026_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
if (v_isShared_2022_ == 0)
{
v___x_2024_ = v___x_2021_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2019_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
else
{
lean_object* v___x_2027_; lean_object* v___x_2029_; 
lean_dec(v___x_1945_);
lean_dec(v_indName_1933_);
v___x_2027_ = lean_box(0);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_2027_);
v___x_2029_ = v___x_1949_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2032_, lean_object* v___x_2033_, lean_object* v___y_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
uint8_t v___x_36864__boxed_2039_; lean_object* v_res_2040_; 
v___x_36864__boxed_2039_ = lean_unbox(v___x_2033_);
v_res_2040_ = l_mkCtorIdx___lam__3(v_indName_2032_, v___x_36864__boxed_2039_, v___y_2034_, v___y_2035_, v___y_2036_, v___y_2037_);
lean_dec(v___y_2037_);
lean_dec_ref(v___y_2036_);
lean_dec(v___y_2035_);
lean_dec_ref(v___y_2034_);
return v_res_2040_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__4(lean_object* v___x_2041_, lean_object* v_e_2042_){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = l_Lean_indentD(v_e_2042_);
v___x_2044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2041_);
lean_ctor_set(v___x_2044_, 1, v___x_2043_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5(lean_object* v___f_2045_, lean_object* v___f_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v___x_2052_; 
v___x_2052_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2045_, v___f_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2052_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
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
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
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
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
v_a_2061_ = lean_ctor_get(v___x_2052_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2052_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2052_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2052_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___lam__5___boxed(lean_object* v___f_2069_, lean_object* v___f_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_mkCtorIdx___lam__5(v___f_2069_, v___f_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2076_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = ((lean_object*)(l_mkCtorIdx___closed__0));
v___x_2079_ = l_Lean_stringToMessageData(v___x_2078_);
return v___x_2079_;
}
}
static lean_object* _init_l_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = ((lean_object*)(l_mkCtorIdx___closed__2));
v___x_2082_ = l_Lean_stringToMessageData(v___x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx(lean_object* v_indName_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; lean_object* v___f_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___f_2097_; lean_object* v___f_2098_; uint8_t v___x_2099_; 
v___x_2089_ = lean_obj_once(&l_mkCtorIdx___closed__1, &l_mkCtorIdx___closed__1_once, _init_l_mkCtorIdx___closed__1);
v___x_2090_ = 0;
v___x_2091_ = lean_box(v___x_2090_);
lean_inc_n(v_indName_2083_, 2);
v___f_2092_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2092_, 0, v_indName_2083_);
lean_closure_set(v___f_2092_, 1, v___x_2091_);
v___x_2093_ = l_Lean_MessageData_ofConstName(v_indName_2083_, v___x_2090_);
v___x_2094_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2089_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = lean_obj_once(&l_mkCtorIdx___closed__3, &l_mkCtorIdx___closed__3_once, _init_l_mkCtorIdx___closed__3);
v___x_2096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___f_2097_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2097_, 0, v___x_2096_);
v___f_2098_ = lean_alloc_closure((void*)(l_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2098_, 0, v___f_2092_);
lean_closure_set(v___f_2098_, 1, v___f_2097_);
v___x_2099_ = l_Lean_isPrivateName(v_indName_2083_);
lean_dec(v_indName_2083_);
if (v___x_2099_ == 0)
{
uint8_t v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = 1;
v___x_2101_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2098_, v___x_2100_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
return v___x_2101_;
}
else
{
lean_object* v___x_2102_; 
v___x_2102_ = l_Lean_withExporting___at___00mkCtorIdx_spec__14___redArg(v___f_2098_, v___x_2090_, v_a_2084_, v_a_2085_, v_a_2086_, v_a_2087_);
return v___x_2102_;
}
}
}
LEAN_EXPORT lean_object* l_mkCtorIdx___boxed(lean_object* v_indName_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_mkCtorIdx(v_indName_2103_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_);
lean_dec(v_a_2107_);
lean_dec_ref(v_a_2106_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(uint8_t v___x_2110_, lean_object* v___x_2111_, lean_object* v_as_2112_, lean_object* v_as_x27_2113_, lean_object* v_b_2114_, lean_object* v_a_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___redArg(v___x_2110_, v___x_2111_, v_as_x27_2113_, v_b_2114_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6___boxed(lean_object* v___x_2122_, lean_object* v___x_2123_, lean_object* v_as_2124_, lean_object* v_as_x27_2125_, lean_object* v_b_2126_, lean_object* v_a_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
uint8_t v___x_37171__boxed_2133_; lean_object* v_res_2134_; 
v___x_37171__boxed_2133_ = lean_unbox(v___x_2122_);
v_res_2134_ = l_List_forIn_x27_loop___at___00mkCtorIdx_spec__6(v___x_37171__boxed_2133_, v___x_2123_, v_as_2124_, v_as_x27_2125_, v_b_2126_, v_a_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v_as_2124_);
lean_dec_ref(v___x_2123_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2135_, lean_object* v_name_2136_, uint8_t v_bi_2137_, lean_object* v_type_2138_, lean_object* v_k_2139_, uint8_t v_kind_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___redArg(v_name_2136_, v_bi_2137_, v_type_2138_, v_k_2139_, v_kind_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_name_2148_, lean_object* v_bi_2149_, lean_object* v_type_2150_, lean_object* v_k_2151_, lean_object* v_kind_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
uint8_t v_bi_boxed_2158_; uint8_t v_kind_boxed_2159_; lean_object* v_res_2160_; 
v_bi_boxed_2158_ = lean_unbox(v_bi_2149_);
v_kind_boxed_2159_ = lean_unbox(v_kind_2152_);
v_res_2160_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7_spec__10(v_00_u03b1_2147_, v_name_2148_, v_bi_boxed_2158_, v_type_2150_, v_k_2151_, v_kind_boxed_2159_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(lean_object* v_00_u03b1_2161_, lean_object* v_name_2162_, lean_object* v_type_2163_, lean_object* v_k_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___redArg(v_name_2162_, v_type_2163_, v_k_2164_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2171_, lean_object* v_name_2172_, lean_object* v_type_2173_, lean_object* v_k_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Meta_withLocalDeclD___at___00mkCtorIdx_spec__7(v_00_u03b1_2171_, v_name_2172_, v_type_2173_, v_k_2174_, v___y_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v___y_2177_);
lean_dec(v___y_2176_);
lean_dec_ref(v___y_2175_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(lean_object* v_declName_2181_, uint8_t v_s_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___redArg(v_declName_2181_, v_s_2182_, v___y_2184_, v___y_2186_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_declName_2189_, lean_object* v_s_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
uint8_t v_s_boxed_2196_; lean_object* v_res_2197_; 
v_s_boxed_2196_ = lean_unbox(v_s_2190_);
v_res_2197_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkCtorIdx_spec__10_spec__15(v_declName_2189_, v_s_boxed_2196_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_);
lean_dec(v___y_2194_);
lean_dec_ref(v___y_2193_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(lean_object* v_env_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___redArg(v_env_2198_, v___y_2200_, v___y_2202_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17___boxed(lean_object* v_env_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00mkCtorIdx_spec__11_spec__17(v_env_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(lean_object* v_00_u03b1_2212_, lean_object* v_bs_2213_, lean_object* v_k_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___redArg(v_bs_2213_, v_k_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
return v___x_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20___boxed(lean_object* v_00_u03b1_2221_, lean_object* v_bs_2222_, lean_object* v_k_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_res_2229_; 
v_res_2229_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12_spec__20(v_00_u03b1_2221_, v_bs_2222_, v_k_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_bs_2222_);
return v_res_2229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(lean_object* v_00_u03b1_2230_, lean_object* v_bs_2231_, lean_object* v_k_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___redArg(v_bs_2231_, v_k_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_2239_, lean_object* v_bs_2240_, lean_object* v_k_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_Meta_withImplicitBinderInfos___at___00mkCtorIdx_spec__12(v_00_u03b1_2239_, v_bs_2240_, v_k_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2248_, lean_object* v_constName_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; 
v___x_2255_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___redArg(v_constName_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2256_, lean_object* v_constName_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2(v_00_u03b1_2256_, v_constName_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2264_, lean_object* v_msg_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_){
_start:
{
lean_object* v___x_2271_; 
v___x_2271_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___redArg(v_msg_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2272_, lean_object* v_msg_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00mkCtorIdx_spec__4_spec__5(v_00_u03b1_2272_, v_msg_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
return v_res_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2280_, lean_object* v_ref_2281_, lean_object* v_constName_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2281_, v_constName_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2289_, lean_object* v_ref_2290_, lean_object* v_constName_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2289_, v_ref_2290_, v_constName_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v_ref_2290_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object* v_00_u03b1_2298_, lean_object* v_ref_2299_, lean_object* v_msg_2300_, lean_object* v_declHint_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_2299_, v_msg_2300_, v_declHint_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_ref_2309_, lean_object* v_msg_2310_, lean_object* v_declHint_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_res_2317_; 
v_res_2317_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_2308_, v_ref_2309_, v_msg_2310_, v_declHint_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v_ref_2309_);
return v_res_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object* v_msg_2318_, lean_object* v_declHint_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_2318_, v_declHint_2319_, v___y_2323_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object* v_msg_2326_, lean_object* v_declHint_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_2326_, v_declHint_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object* v_00_u03b1_2334_, lean_object* v_ref_2335_, lean_object* v_msg_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_2335_, v_msg_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2343_, lean_object* v_ref_2344_, lean_object* v_msg_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_2343_, v_ref_2344_, v_msg_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v_ref_2344_);
return v_res_2351_;
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
