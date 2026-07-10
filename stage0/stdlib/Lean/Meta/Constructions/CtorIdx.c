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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addToCompletionBlackList(lean_object*, lean_object*);
lean_object* l_Lean_addProtected(lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
extern lean_object* l_Lean_Linter_deprecatedAttr;
lean_object* l_Lean_ParametricAttribute_setParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
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
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Lean_getMaxHeight(lean_object*, lean_object*);
uint32_t lean_uint32_add(uint32_t, uint32_t);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isInductiveCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "genCtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(121, 142, 77, 16, 50, 110, 46, 202)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "generate the `CtorIdx` functions for inductive datatypes"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CtorIdx"};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(149, 119, 104, 54, 230, 159, 208, 234)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 246, 214, 203, 234, 6, 143, 204)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(57, 215, 55, 153, 7, 83, 44, 161)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),((lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(35, 209, 53, 49, 90, 19, 84, 123)}};
static const lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
static const lean_string_object l_Lean_mkToCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toCtorIdx"};
static const lean_object* l_Lean_mkToCtorIdxName___closed__0 = (const lean_object*)&l_Lean_mkToCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkToCtorIdxName(lean_object*);
static const lean_string_object l_Lean_mkCtorIdxName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ctorIdx"};
static const lean_object* l_Lean_mkCtorIdxName___closed__0 = (const lean_object*)&l_Lean_mkCtorIdxName___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_mkCtorIdx_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_mkCtorIdx_spec__13___closed__0 = (const lean_object*)&l_panic___at___00Lean_mkCtorIdx_spec__13___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5_value;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCtorIdx___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "2025-08-25"};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__0_value)}};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__1_value;
static const lean_string_object l_Lean_mkCtorIdx___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__2 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l_Lean_mkCtorIdx___lam__1___closed__3 = (const lean_object*)&l_Lean_mkCtorIdx___lam__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_mkCtorIdx___lam__2___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_mkCtorIdx___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_mkCtorIdx___lam__2___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Meta.Constructions.CtorIdx"};
static const lean_object* l_Lean_mkCtorIdx___lam__3___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___lam__3___closed__0_value;
static const lean_string_object l_Lean_mkCtorIdx___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Lean.mkCtorIdx"};
static const lean_object* l_Lean_mkCtorIdx___lam__3___closed__1 = (const lean_object*)&l_Lean_mkCtorIdx___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_mkCtorIdx___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCtorIdx___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "failed to construct `T.ctorIdx` for `"};
static const lean_object* l_Lean_mkCtorIdx___closed__0 = (const lean_object*)&l_Lean_mkCtorIdx___closed__0_value;
static lean_once_cell_t l_Lean_mkCtorIdx___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___closed__1;
static const lean_string_object l_Lean_mkCtorIdx___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l_Lean_mkCtorIdx___closed__2 = (const lean_object*)&l_Lean_mkCtorIdx___closed__2_value;
static lean_once_cell_t l_Lean_mkCtorIdx___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCtorIdx___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_73_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_74_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_75_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_));
v___x_76_ = l_Lean_Option_register___at___00__private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4__spec__0(v___x_73_, v___x_74_, v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4____boxed(lean_object* v_a_77_){
_start:
{
lean_object* v_res_78_; 
v_res_78_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkToCtorIdxName(lean_object* v_indName_80_){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Lean_mkToCtorIdxName___closed__0));
v___x_82_ = l_Lean_Name_str___override(v_indName_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdxName(lean_object* v_indName_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_86_ = l_Lean_Name_str___override(v_indName_84_, v___x_85_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdxCore_x3f(lean_object* v_env_87_, lean_object* v_declName_88_){
_start:
{
if (lean_obj_tag(v_declName_88_) == 1)
{
lean_object* v_pre_89_; lean_object* v_str_90_; lean_object* v___x_91_; uint8_t v___x_92_; 
v_pre_89_ = lean_ctor_get(v_declName_88_, 0);
lean_inc(v_pre_89_);
v_str_90_ = lean_ctor_get(v_declName_88_, 1);
lean_inc_ref(v_str_90_);
lean_dec_ref_known(v_declName_88_, 2);
v___x_91_ = ((lean_object*)(l_Lean_mkCtorIdxName___closed__0));
v___x_92_ = lean_string_dec_eq(v_str_90_, v___x_91_);
lean_dec_ref(v_str_90_);
if (v___x_92_ == 0)
{
lean_object* v___x_93_; 
lean_dec(v_pre_89_);
lean_dec_ref(v_env_87_);
v___x_93_ = lean_box(0);
return v___x_93_;
}
else
{
lean_object* v___x_94_; 
v___x_94_ = l_Lean_isInductiveCore_x3f(v_env_87_, v_pre_89_);
return v___x_94_;
}
}
else
{
lean_object* v___x_95_; 
lean_dec(v_declName_88_);
lean_dec_ref(v_env_87_);
v___x_95_ = lean_box(0);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg(lean_object* v_declName_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_99_; lean_object* v_env_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_st_ref_get(v_a_97_);
v_env_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc_ref(v_env_100_);
lean_dec(v___x_99_);
v___x_101_ = l_Lean_isCtorIdxCore_x3f(v_env_100_, v_declName_96_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___redArg___boxed(lean_object* v_declName_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_103_, v_a_104_);
lean_dec(v_a_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f(lean_object* v_declName_107_, lean_object* v_a_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_isCtorIdx_x3f___redArg(v_declName_107_, v_a_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtorIdx_x3f___boxed(lean_object* v_declName_114_, lean_object* v_a_115_, lean_object* v_a_116_, lean_object* v_a_117_, lean_object* v_a_118_, lean_object* v_a_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_isCtorIdx_x3f(v_declName_114_, v_a_115_, v_a_116_, v_a_117_, v_a_118_);
lean_dec(v_a_118_);
lean_dec_ref(v_a_117_);
lean_dec(v_a_116_);
lean_dec_ref(v_a_115_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(lean_object* v_opts_121_, lean_object* v_opt_122_){
_start:
{
lean_object* v_name_123_; lean_object* v_defValue_124_; lean_object* v_map_125_; lean_object* v___x_126_; 
v_name_123_ = lean_ctor_get(v_opt_122_, 0);
v_defValue_124_ = lean_ctor_get(v_opt_122_, 1);
v_map_125_ = lean_ctor_get(v_opts_121_, 0);
v___x_126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_125_, v_name_123_);
if (lean_obj_tag(v___x_126_) == 0)
{
uint8_t v___x_127_; 
v___x_127_ = lean_unbox(v_defValue_124_);
return v___x_127_;
}
else
{
lean_object* v_val_128_; 
v_val_128_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_val_128_);
lean_dec_ref_known(v___x_126_, 1);
if (lean_obj_tag(v_val_128_) == 1)
{
uint8_t v_v_129_; 
v_v_129_ = lean_ctor_get_uint8(v_val_128_, 0);
lean_dec_ref_known(v_val_128_, 0);
return v_v_129_;
}
else
{
uint8_t v___x_130_; 
lean_dec(v_val_128_);
v___x_130_ = lean_unbox(v_defValue_124_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0___boxed(lean_object* v_opts_131_, lean_object* v_opt_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_opts_131_, v_opt_132_);
lean_dec_ref(v_opt_132_);
lean_dec_ref(v_opts_131_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(lean_object* v_constName_135_, uint8_t v_skipRealize_136_, lean_object* v___y_137_){
_start:
{
lean_object* v___x_139_; lean_object* v_env_140_; uint8_t v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_139_ = lean_st_ref_get(v___y_137_);
v_env_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc_ref(v_env_140_);
lean_dec(v___x_139_);
v___x_141_ = l_Lean_Environment_contains(v_env_140_, v_constName_135_, v_skipRealize_136_);
v___x_142_ = lean_box(v___x_141_);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg___boxed(lean_object* v_constName_144_, lean_object* v_skipRealize_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
uint8_t v_skipRealize_boxed_148_; lean_object* v_res_149_; 
v_skipRealize_boxed_148_ = lean_unbox(v_skipRealize_145_);
v_res_149_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_144_, v_skipRealize_boxed_148_, v___y_146_);
lean_dec(v___y_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(lean_object* v_constName_150_, uint8_t v_skipRealize_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v_constName_150_, v_skipRealize_151_, v___y_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___boxed(lean_object* v_constName_158_, lean_object* v_skipRealize_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
uint8_t v_skipRealize_boxed_165_; lean_object* v_res_166_; 
v_skipRealize_boxed_165_ = lean_unbox(v_skipRealize_159_);
v_res_166_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1(v_constName_158_, v_skipRealize_boxed_165_, v___y_160_, v___y_161_, v___y_162_, v___y_163_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0(lean_object* v_k_167_, lean_object* v_b_168_, lean_object* v_c_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_175_; 
lean_inc(v___y_173_);
lean_inc_ref(v___y_172_);
lean_inc(v___y_171_);
lean_inc_ref(v___y_170_);
v___x_175_ = lean_apply_7(v_k_167_, v_b_168_, v_c_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_, lean_box(0));
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0___boxed(lean_object* v_k_176_, lean_object* v_b_177_, lean_object* v_c_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_, lean_object* v___y_182_, lean_object* v___y_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0(v_k_176_, v_b_177_, v_c_178_, v___y_179_, v___y_180_, v___y_181_, v___y_182_);
lean_dec(v___y_182_);
lean_dec_ref(v___y_181_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(lean_object* v_type_185_, lean_object* v_maxFVars_x3f_186_, lean_object* v_k_187_, uint8_t v_cleanupAnnotations_188_, uint8_t v_whnfType_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v___f_195_; lean_object* v___x_196_; 
v___f_195_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_195_, 0, v_k_187_);
v___x_196_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_185_, v_maxFVars_x3f_186_, v___f_195_, v_cleanupAnnotations_188_, v_whnfType_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
v_a_205_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_196_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_196_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg___boxed(lean_object* v_type_213_, lean_object* v_maxFVars_x3f_214_, lean_object* v_k_215_, lean_object* v_cleanupAnnotations_216_, lean_object* v_whnfType_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_223_; uint8_t v_whnfType_boxed_224_; lean_object* v_res_225_; 
v_cleanupAnnotations_boxed_223_ = lean_unbox(v_cleanupAnnotations_216_);
v_whnfType_boxed_224_ = lean_unbox(v_whnfType_217_);
v_res_225_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_213_, v_maxFVars_x3f_214_, v_k_215_, v_cleanupAnnotations_boxed_223_, v_whnfType_boxed_224_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(lean_object* v_00_u03b1_226_, lean_object* v_type_227_, lean_object* v_maxFVars_x3f_228_, lean_object* v_k_229_, uint8_t v_cleanupAnnotations_230_, uint8_t v_whnfType_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_227_, v_maxFVars_x3f_228_, v_k_229_, v_cleanupAnnotations_230_, v_whnfType_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___boxed(lean_object* v_00_u03b1_238_, lean_object* v_type_239_, lean_object* v_maxFVars_x3f_240_, lean_object* v_k_241_, lean_object* v_cleanupAnnotations_242_, lean_object* v_whnfType_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_249_; uint8_t v_whnfType_boxed_250_; lean_object* v_res_251_; 
v_cleanupAnnotations_boxed_249_ = lean_unbox(v_cleanupAnnotations_242_);
v_whnfType_boxed_250_ = lean_unbox(v_whnfType_243_);
v_res_251_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5(v_00_u03b1_238_, v_type_239_, v_maxFVars_x3f_240_, v_k_241_, v_cleanupAnnotations_boxed_249_, v_whnfType_boxed_250_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(lean_object* v_name_252_, lean_object* v_levelParams_253_, lean_object* v_type_254_, lean_object* v_value_255_, lean_object* v_hints_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; uint8_t v___y_261_; uint8_t v___y_268_; lean_object* v_env_271_; uint8_t v___x_272_; 
v___x_259_ = lean_st_ref_get(v___y_257_);
v_env_271_ = lean_ctor_get(v___x_259_, 0);
lean_inc_ref_n(v_env_271_, 2);
lean_dec(v___x_259_);
v___x_272_ = l_Lean_Environment_hasUnsafe(v_env_271_, v_type_254_);
if (v___x_272_ == 0)
{
uint8_t v___x_273_; 
v___x_273_ = l_Lean_Environment_hasUnsafe(v_env_271_, v_value_255_);
v___y_268_ = v___x_273_;
goto v___jp_267_;
}
else
{
lean_dec_ref(v_env_271_);
v___y_268_ = v___x_272_;
goto v___jp_267_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
lean_inc(v_name_252_);
v___x_262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_262_, 0, v_name_252_);
lean_ctor_set(v___x_262_, 1, v_levelParams_253_);
lean_ctor_set(v___x_262_, 2, v_type_254_);
v___x_263_ = lean_box(0);
v___x_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_264_, 0, v_name_252_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_265_, 0, v___x_262_);
lean_ctor_set(v___x_265_, 1, v_value_255_);
lean_ctor_set(v___x_265_, 2, v_hints_256_);
lean_ctor_set(v___x_265_, 3, v___x_264_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*4, v___y_261_);
v___x_266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
return v___x_266_;
}
v___jp_267_:
{
if (v___y_268_ == 0)
{
uint8_t v___x_269_; 
v___x_269_ = 1;
v___y_261_ = v___x_269_;
goto v___jp_260_;
}
else
{
uint8_t v___x_270_; 
v___x_270_ = 0;
v___y_261_ = v___x_270_;
goto v___jp_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg___boxed(lean_object* v_name_274_, lean_object* v_levelParams_275_, lean_object* v_type_276_, lean_object* v_value_277_, lean_object* v_hints_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_274_, v_levelParams_275_, v_type_276_, v_value_277_, v_hints_278_, v___y_279_);
lean_dec(v___y_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(lean_object* v_name_282_, lean_object* v_levelParams_283_, lean_object* v_type_284_, lean_object* v_value_285_, lean_object* v_hints_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v_name_282_, v_levelParams_283_, v_type_284_, v_value_285_, v_hints_286_, v___y_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___boxed(lean_object* v_name_293_, lean_object* v_levelParams_294_, lean_object* v_type_295_, lean_object* v_value_296_, lean_object* v_hints_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8(v_name_293_, v_levelParams_294_, v_type_295_, v_value_296_, v_hints_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__13(lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___f_311_; lean_object* v___x_26624__overap_312_; lean_object* v___x_313_; 
v___f_311_ = ((lean_object*)(l_panic___at___00Lean_mkCtorIdx_spec__13___closed__0));
v___x_26624__overap_312_ = lean_panic_fn_borrowed(v___f_311_, v_msg_305_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
v___x_313_ = lean_apply_5(v___x_26624__overap_312_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, lean_box(0));
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_mkCtorIdx_spec__13___boxed(lean_object* v_msg_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_panic___at___00Lean_mkCtorIdx_spec__13(v_msg_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0(lean_object* v___y_321_, uint8_t v_isExporting_322_, lean_object* v___x_323_, lean_object* v___y_324_, lean_object* v___x_325_, lean_object* v_a_x3f_326_){
_start:
{
lean_object* v___x_328_; lean_object* v_env_329_; lean_object* v_nextMacroScope_330_; lean_object* v_ngen_331_; lean_object* v_auxDeclNGen_332_; lean_object* v_traceState_333_; lean_object* v_messages_334_; lean_object* v_infoState_335_; lean_object* v_snapshotTasks_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_361_; 
v___x_328_ = lean_st_ref_take(v___y_321_);
v_env_329_ = lean_ctor_get(v___x_328_, 0);
v_nextMacroScope_330_ = lean_ctor_get(v___x_328_, 1);
v_ngen_331_ = lean_ctor_get(v___x_328_, 2);
v_auxDeclNGen_332_ = lean_ctor_get(v___x_328_, 3);
v_traceState_333_ = lean_ctor_get(v___x_328_, 4);
v_messages_334_ = lean_ctor_get(v___x_328_, 6);
v_infoState_335_ = lean_ctor_get(v___x_328_, 7);
v_snapshotTasks_336_ = lean_ctor_get(v___x_328_, 8);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; 
v_unused_362_ = lean_ctor_get(v___x_328_, 5);
lean_dec(v_unused_362_);
v___x_338_ = v___x_328_;
v_isShared_339_ = v_isSharedCheck_361_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_snapshotTasks_336_);
lean_inc(v_infoState_335_);
lean_inc(v_messages_334_);
lean_inc(v_traceState_333_);
lean_inc(v_auxDeclNGen_332_);
lean_inc(v_ngen_331_);
lean_inc(v_nextMacroScope_330_);
lean_inc(v_env_329_);
lean_dec(v___x_328_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_361_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = l_Lean_Environment_setExporting(v_env_329_, v_isExporting_322_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 5, v___x_323_);
lean_ctor_set(v___x_338_, 0, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_nextMacroScope_330_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_ngen_331_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_auxDeclNGen_332_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v_traceState_333_);
lean_ctor_set(v_reuseFailAlloc_360_, 5, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_360_, 6, v_messages_334_);
lean_ctor_set(v_reuseFailAlloc_360_, 7, v_infoState_335_);
lean_ctor_set(v_reuseFailAlloc_360_, 8, v_snapshotTasks_336_);
v___x_342_ = v_reuseFailAlloc_360_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_mctx_345_; lean_object* v_zetaDeltaFVarIds_346_; lean_object* v_postponed_347_; lean_object* v_diag_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_358_; 
v___x_343_ = lean_st_ref_set(v___y_321_, v___x_342_);
v___x_344_ = lean_st_ref_take(v___y_324_);
v_mctx_345_ = lean_ctor_get(v___x_344_, 0);
v_zetaDeltaFVarIds_346_ = lean_ctor_get(v___x_344_, 2);
v_postponed_347_ = lean_ctor_get(v___x_344_, 3);
v_diag_348_ = lean_ctor_get(v___x_344_, 4);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_358_ == 0)
{
lean_object* v_unused_359_; 
v_unused_359_ = lean_ctor_get(v___x_344_, 1);
lean_dec(v_unused_359_);
v___x_350_ = v___x_344_;
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_diag_348_);
lean_inc(v_postponed_347_);
lean_inc(v_zetaDeltaFVarIds_346_);
lean_inc(v_mctx_345_);
lean_dec(v___x_344_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_358_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_325_);
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_mctx_345_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_zetaDeltaFVarIds_346_);
lean_ctor_set(v_reuseFailAlloc_357_, 3, v_postponed_347_);
lean_ctor_set(v_reuseFailAlloc_357_, 4, v_diag_348_);
v___x_353_ = v_reuseFailAlloc_357_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_st_ref_set(v___y_324_, v___x_353_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0___boxed(lean_object* v___y_363_, lean_object* v_isExporting_364_, lean_object* v___x_365_, lean_object* v___y_366_, lean_object* v___x_367_, lean_object* v_a_x3f_368_, lean_object* v___y_369_){
_start:
{
uint8_t v_isExporting_boxed_370_; lean_object* v_res_371_; 
v_isExporting_boxed_370_ = lean_unbox(v_isExporting_364_);
v_res_371_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0(v___y_363_, v_isExporting_boxed_370_, v___x_365_, v___y_366_, v___x_367_, v_a_x3f_368_);
lean_dec(v_a_x3f_368_);
lean_dec(v___y_366_);
lean_dec(v___y_363_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__0(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_372_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__0, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__0);
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
return v___x_374_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2(void){
_start:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3(void){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__1);
v___x_378_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
lean_ctor_set(v___x_378_, 2, v___x_377_);
lean_ctor_set(v___x_378_, 3, v___x_377_);
lean_ctor_set(v___x_378_, 4, v___x_377_);
lean_ctor_set(v___x_378_, 5, v___x_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(lean_object* v_x_379_, uint8_t v_isExporting_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; lean_object* v_env_387_; uint8_t v_isExporting_388_; uint8_t v___y_455_; lean_object* v___x_457_; uint8_t v_isModule_458_; uint8_t v___x_459_; 
v___x_386_ = lean_st_ref_get(v___y_384_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
v_isExporting_388_ = lean_ctor_get_uint8(v_env_387_, sizeof(void*)*8);
v___x_457_ = l_Lean_Environment_header(v_env_387_);
lean_dec_ref(v_env_387_);
v_isModule_458_ = lean_ctor_get_uint8(v___x_457_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_bool_not(v_isModule_458_);
if (v___x_459_ == 0)
{
if (v_isExporting_388_ == 0)
{
if (v_isExporting_380_ == 0)
{
lean_object* v___x_460_; 
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
v___x_460_ = lean_apply_5(v_x_379_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, lean_box(0));
return v___x_460_;
}
else
{
goto v___jp_389_;
}
}
else
{
v___y_455_ = v_isExporting_380_;
goto v___jp_454_;
}
}
else
{
v___y_455_ = v___x_459_;
goto v___jp_454_;
}
v___jp_389_:
{
lean_object* v___x_390_; lean_object* v_env_391_; lean_object* v_nextMacroScope_392_; lean_object* v_ngen_393_; lean_object* v_auxDeclNGen_394_; lean_object* v_traceState_395_; lean_object* v_messages_396_; lean_object* v_infoState_397_; lean_object* v_snapshotTasks_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_452_; 
v___x_390_ = lean_st_ref_take(v___y_384_);
v_env_391_ = lean_ctor_get(v___x_390_, 0);
v_nextMacroScope_392_ = lean_ctor_get(v___x_390_, 1);
v_ngen_393_ = lean_ctor_get(v___x_390_, 2);
v_auxDeclNGen_394_ = lean_ctor_get(v___x_390_, 3);
v_traceState_395_ = lean_ctor_get(v___x_390_, 4);
v_messages_396_ = lean_ctor_get(v___x_390_, 6);
v_infoState_397_ = lean_ctor_get(v___x_390_, 7);
v_snapshotTasks_398_ = lean_ctor_get(v___x_390_, 8);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_452_ == 0)
{
lean_object* v_unused_453_; 
v_unused_453_ = lean_ctor_get(v___x_390_, 5);
lean_dec(v_unused_453_);
v___x_400_ = v___x_390_;
v_isShared_401_ = v_isSharedCheck_452_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_snapshotTasks_398_);
lean_inc(v_infoState_397_);
lean_inc(v_messages_396_);
lean_inc(v_traceState_395_);
lean_inc(v_auxDeclNGen_394_);
lean_inc(v_ngen_393_);
lean_inc(v_nextMacroScope_392_);
lean_inc(v_env_391_);
lean_dec(v___x_390_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_452_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_402_ = l_Lean_Environment_setExporting(v_env_391_, v_isExporting_380_);
v___x_403_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 5, v___x_403_);
lean_ctor_set(v___x_400_, 0, v___x_402_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_nextMacroScope_392_);
lean_ctor_set(v_reuseFailAlloc_451_, 2, v_ngen_393_);
lean_ctor_set(v_reuseFailAlloc_451_, 3, v_auxDeclNGen_394_);
lean_ctor_set(v_reuseFailAlloc_451_, 4, v_traceState_395_);
lean_ctor_set(v_reuseFailAlloc_451_, 5, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_451_, 6, v_messages_396_);
lean_ctor_set(v_reuseFailAlloc_451_, 7, v_infoState_397_);
lean_ctor_set(v_reuseFailAlloc_451_, 8, v_snapshotTasks_398_);
v___x_405_ = v_reuseFailAlloc_451_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v_mctx_408_; lean_object* v_zetaDeltaFVarIds_409_; lean_object* v_postponed_410_; lean_object* v_diag_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_449_; 
v___x_406_ = lean_st_ref_set(v___y_384_, v___x_405_);
v___x_407_ = lean_st_ref_take(v___y_382_);
v_mctx_408_ = lean_ctor_get(v___x_407_, 0);
v_zetaDeltaFVarIds_409_ = lean_ctor_get(v___x_407_, 2);
v_postponed_410_ = lean_ctor_get(v___x_407_, 3);
v_diag_411_ = lean_ctor_get(v___x_407_, 4);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_449_ == 0)
{
lean_object* v_unused_450_; 
v_unused_450_ = lean_ctor_get(v___x_407_, 1);
lean_dec(v_unused_450_);
v___x_413_ = v___x_407_;
v_isShared_414_ = v_isSharedCheck_449_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_diag_411_);
lean_inc(v_postponed_410_);
lean_inc(v_zetaDeltaFVarIds_409_);
lean_inc(v_mctx_408_);
lean_dec(v___x_407_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_449_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_415_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_415_);
v___x_417_ = v___x_413_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_mctx_408_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_448_, 2, v_zetaDeltaFVarIds_409_);
lean_ctor_set(v_reuseFailAlloc_448_, 3, v_postponed_410_);
lean_ctor_set(v_reuseFailAlloc_448_, 4, v_diag_411_);
v___x_417_ = v_reuseFailAlloc_448_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; lean_object* v_r_419_; 
v___x_418_ = lean_st_ref_set(v___y_382_, v___x_417_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
v_r_419_ = lean_apply_5(v_x_379_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, lean_box(0));
if (lean_obj_tag(v_r_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_436_; 
v_a_420_ = lean_ctor_get(v_r_419_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_r_419_);
if (v_isSharedCheck_436_ == 0)
{
v___x_422_ = v_r_419_;
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v_r_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_436_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
lean_inc(v_a_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set_tag(v___x_422_, 1);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_420_);
v___x_425_ = v_reuseFailAlloc_435_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_433_; 
v___x_426_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0(v___y_384_, v_isExporting_388_, v___x_403_, v___y_382_, v___x_415_, v___x_425_);
lean_dec_ref(v___x_425_);
v_isSharedCheck_433_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_433_ == 0)
{
lean_object* v_unused_434_; 
v_unused_434_ = lean_ctor_get(v___x_426_, 0);
lean_dec(v_unused_434_);
v___x_428_ = v___x_426_;
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
else
{
lean_dec(v___x_426_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_433_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_431_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 0, v_a_420_);
v___x_431_ = v___x_428_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_a_420_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
else
{
lean_object* v_a_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_446_; 
v_a_437_ = lean_ctor_get(v_r_419_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v_r_419_, 1);
v___x_438_ = lean_box(0);
v___x_439_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0(v___y_384_, v_isExporting_388_, v___x_403_, v___y_382_, v___x_415_, v___x_438_);
v_isSharedCheck_446_ = !lean_is_exclusive(v___x_439_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; 
v_unused_447_ = lean_ctor_get(v___x_439_, 0);
lean_dec(v_unused_447_);
v___x_441_ = v___x_439_;
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
else
{
lean_dec(v___x_439_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_446_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_444_; 
if (v_isShared_442_ == 0)
{
lean_ctor_set_tag(v___x_441_, 1);
lean_ctor_set(v___x_441_, 0, v_a_437_);
v___x_444_ = v___x_441_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_a_437_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
}
}
}
}
v___jp_454_:
{
if (v___y_455_ == 0)
{
goto v___jp_389_;
}
else
{
lean_object* v___x_456_; 
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
v___x_456_ = lean_apply_5(v_x_379_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, lean_box(0));
return v___x_456_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___boxed(lean_object* v_x_461_, lean_object* v_isExporting_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v_isExporting_boxed_468_; lean_object* v_res_469_; 
v_isExporting_boxed_468_ = lean_unbox(v_isExporting_462_);
v_res_469_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v_x_461_, v_isExporting_boxed_468_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14(lean_object* v_00_u03b1_470_, lean_object* v_x_471_, uint8_t v_isExporting_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v_x_471_, v_isExporting_472_, v___y_473_, v___y_474_, v___y_475_, v___y_476_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___boxed(lean_object* v_00_u03b1_479_, lean_object* v_x_480_, lean_object* v_isExporting_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
uint8_t v_isExporting_boxed_487_; lean_object* v_res_488_; 
v_isExporting_boxed_487_ = lean_unbox(v_isExporting_481_);
v_res_488_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14(v_00_u03b1_479_, v_x_480_, v_isExporting_boxed_487_, v___y_482_, v___y_483_, v___y_484_, v___y_485_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_489_, uint8_t v___x_490_, uint8_t v___x_491_, uint8_t v___x_492_, lean_object* v_ys_493_, lean_object* v_x_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = l_Lean_mkRawNatLit(v_cidx_489_);
v___x_501_ = l_Lean_Meta_mkLambdaFVars(v_ys_493_, v___x_500_, v___x_490_, v___x_491_, v___x_490_, v___x_491_, v___x_492_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_502_, lean_object* v___x_503_, lean_object* v___x_504_, lean_object* v___x_505_, lean_object* v_ys_506_, lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
uint8_t v___x_34529__boxed_513_; uint8_t v___x_34530__boxed_514_; uint8_t v___x_34531__boxed_515_; lean_object* v_res_516_; 
v___x_34529__boxed_513_ = lean_unbox(v___x_503_);
v___x_34530__boxed_514_ = lean_unbox(v___x_504_);
v___x_34531__boxed_515_ = lean_unbox(v___x_505_);
v_res_516_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_502_, v___x_34529__boxed_513_, v___x_34530__boxed_514_, v___x_34531__boxed_515_, v_ys_506_, v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec_ref(v_x_507_);
lean_dec_ref(v_ys_506_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v___x_523_; lean_object* v_env_524_; lean_object* v___x_525_; lean_object* v_mctx_526_; lean_object* v_lctx_527_; lean_object* v_options_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_523_ = lean_st_ref_get(v___y_521_);
v_env_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_env_524_);
lean_dec(v___x_523_);
v___x_525_ = lean_st_ref_get(v___y_519_);
v_mctx_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc_ref(v_mctx_526_);
lean_dec(v___x_525_);
v_lctx_527_ = lean_ctor_get(v___y_518_, 2);
v_options_528_ = lean_ctor_get(v___y_520_, 2);
lean_inc_ref(v_options_528_);
lean_inc_ref(v_lctx_527_);
v___x_529_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_529_, 0, v_env_524_);
lean_ctor_set(v___x_529_, 1, v_mctx_526_);
lean_ctor_set(v___x_529_, 2, v_lctx_527_);
lean_ctor_set(v___x_529_, 3, v_options_528_);
v___x_530_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v_msgData_517_);
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_ref_545_; lean_object* v___x_546_; lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_555_; 
v_ref_545_ = lean_ctor_get(v___y_542_, 5);
v___x_546_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msg_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
v_a_547_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_555_ == 0)
{
v___x_549_ = v___x_546_;
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v___x_546_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_555_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_553_; 
lean_inc(v_ref_545_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_ref_545_);
lean_ctor_set(v___x_551_, 1, v_a_547_);
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 1);
lean_ctor_set(v___x_549_, 0, v___x_551_);
v___x_553_ = v___x_549_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_551_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
return v_res_562_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_instMonadEIO(lean_box(0));
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_toApplicative_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_637_; 
v___x_574_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_575_ = l_StateRefT_x27_instMonad___redArg(v___x_574_);
v_toApplicative_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_637_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_637_ == 0)
{
lean_object* v_unused_638_; 
v_unused_638_ = lean_ctor_get(v___x_575_, 1);
lean_dec(v_unused_638_);
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_637_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_toApplicative_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_637_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v_toFunctor_580_; lean_object* v_toSeq_581_; lean_object* v_toSeqLeft_582_; lean_object* v_toSeqRight_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_635_; 
v_toFunctor_580_ = lean_ctor_get(v_toApplicative_576_, 0);
v_toSeq_581_ = lean_ctor_get(v_toApplicative_576_, 2);
v_toSeqLeft_582_ = lean_ctor_get(v_toApplicative_576_, 3);
v_toSeqRight_583_ = lean_ctor_get(v_toApplicative_576_, 4);
v_isSharedCheck_635_ = !lean_is_exclusive(v_toApplicative_576_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v_toApplicative_576_, 1);
lean_dec(v_unused_636_);
v___x_585_ = v_toApplicative_576_;
v_isShared_586_ = v_isSharedCheck_635_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_toSeqRight_583_);
lean_inc(v_toSeqLeft_582_);
lean_inc(v_toSeq_581_);
lean_inc(v_toFunctor_580_);
lean_dec(v_toApplicative_576_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_635_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___f_589_; lean_object* v___f_590_; lean_object* v___x_591_; lean_object* v___f_592_; lean_object* v___f_593_; lean_object* v___f_594_; lean_object* v___x_596_; 
v___f_587_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_588_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_580_);
v___f_589_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_589_, 0, v_toFunctor_580_);
v___f_590_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_590_, 0, v_toFunctor_580_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___f_589_);
lean_ctor_set(v___x_591_, 1, v___f_590_);
v___f_592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_592_, 0, v_toSeqRight_583_);
v___f_593_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_593_, 0, v_toSeqLeft_582_);
v___f_594_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_594_, 0, v_toSeq_581_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 4, v___f_592_);
lean_ctor_set(v___x_585_, 3, v___f_593_);
lean_ctor_set(v___x_585_, 2, v___f_594_);
lean_ctor_set(v___x_585_, 1, v___f_587_);
lean_ctor_set(v___x_585_, 0, v___x_591_);
v___x_596_ = v___x_585_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___f_587_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v___f_594_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v___f_593_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v___f_592_);
v___x_596_ = v_reuseFailAlloc_634_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v___f_588_);
lean_ctor_set(v___x_578_, 0, v___x_596_);
v___x_598_ = v___x_578_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v___f_588_);
v___x_598_ = v_reuseFailAlloc_633_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v_toApplicative_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_631_; 
v___x_599_ = l_StateRefT_x27_instMonad___redArg(v___x_598_);
v_toApplicative_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_631_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v___x_599_, 1);
lean_dec(v_unused_632_);
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_631_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_toApplicative_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_631_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v_toFunctor_604_; lean_object* v_toSeq_605_; lean_object* v_toSeqLeft_606_; lean_object* v_toSeqRight_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_629_; 
v_toFunctor_604_ = lean_ctor_get(v_toApplicative_600_, 0);
v_toSeq_605_ = lean_ctor_get(v_toApplicative_600_, 2);
v_toSeqLeft_606_ = lean_ctor_get(v_toApplicative_600_, 3);
v_toSeqRight_607_ = lean_ctor_get(v_toApplicative_600_, 4);
v_isSharedCheck_629_ = !lean_is_exclusive(v_toApplicative_600_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_toApplicative_600_, 1);
lean_dec(v_unused_630_);
v___x_609_ = v_toApplicative_600_;
v_isShared_610_ = v_isSharedCheck_629_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_toSeqRight_607_);
lean_inc(v_toSeqLeft_606_);
lean_inc(v_toSeq_605_);
lean_inc(v_toFunctor_604_);
lean_dec(v_toApplicative_600_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_629_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___f_613_; lean_object* v___f_614_; lean_object* v___x_615_; lean_object* v___f_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___x_620_; 
v___f_611_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_612_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_604_);
v___f_613_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_613_, 0, v_toFunctor_604_);
v___f_614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_614_, 0, v_toFunctor_604_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___f_613_);
lean_ctor_set(v___x_615_, 1, v___f_614_);
v___f_616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_616_, 0, v_toSeqRight_607_);
v___f_617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_617_, 0, v_toSeqLeft_606_);
v___f_618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_618_, 0, v_toSeq_605_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 4, v___f_616_);
lean_ctor_set(v___x_609_, 3, v___f_617_);
lean_ctor_set(v___x_609_, 2, v___f_618_);
lean_ctor_set(v___x_609_, 1, v___f_611_);
lean_ctor_set(v___x_609_, 0, v___x_615_);
v___x_620_ = v___x_609_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v___f_611_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v___f_618_);
lean_ctor_set(v_reuseFailAlloc_628_, 3, v___f_617_);
lean_ctor_set(v_reuseFailAlloc_628_, 4, v___f_616_);
v___x_620_ = v_reuseFailAlloc_628_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_622_; 
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v___f_612_);
lean_ctor_set(v___x_602_, 0, v___x_620_);
v___x_622_ = v___x_602_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v___f_612_);
v___x_622_ = v_reuseFailAlloc_627_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_30014__overap_625_; lean_object* v___x_626_; 
v___x_623_ = lean_box(0);
v___x_624_ = l_instInhabitedOfMonad___redArg(v___x_622_, v___x_623_);
v___x_30014__overap_625_ = lean_panic_fn_borrowed(v___x_624_, v_msg_568_);
lean_dec(v___x_624_);
lean_inc(v___y_572_);
lean_inc_ref(v___y_571_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
v___x_626_ = lean_apply_5(v___x_30014__overap_625_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, lean_box(0));
return v___x_626_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
return v_res_645_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_656_ = lean_unsigned_to_nat(11u);
v___x_657_ = lean_unsigned_to_nat(122u);
v___x_658_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_659_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_660_ = l_mkPanicMessageWithDecl(v___x_659_, v___x_658_, v___x_657_, v___x_656_, v___x_655_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v___x_675_; lean_object* v_env_676_; uint8_t v___x_677_; lean_object* v___x_678_; 
v___x_675_ = lean_st_ref_get(v___y_665_);
v_env_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc_ref(v_env_676_);
lean_dec(v___x_675_);
v___x_677_ = 0;
lean_inc(v_constName_661_);
v___x_678_ = l_Lean_Environment_findAsync_x3f(v_env_676_, v_constName_661_, v___x_677_);
if (lean_obj_tag(v___x_678_) == 1)
{
lean_object* v_val_679_; uint8_t v_kind_680_; 
v_val_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v___x_678_, 1);
v_kind_680_ = lean_ctor_get_uint8(v_val_679_, sizeof(void*)*3);
if (v_kind_680_ == 6)
{
lean_object* v___x_681_; 
v___x_681_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_679_);
if (lean_obj_tag(v___x_681_) == 6)
{
lean_object* v_val_682_; lean_object* v___x_684_; uint8_t v_isShared_685_; uint8_t v_isSharedCheck_689_; 
lean_dec(v_constName_661_);
v_val_682_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_689_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_689_ == 0)
{
v___x_684_ = v___x_681_;
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
else
{
lean_inc(v_val_682_);
lean_dec(v___x_681_);
v___x_684_ = lean_box(0);
v_isShared_685_ = v_isSharedCheck_689_;
goto v_resetjp_683_;
}
v_resetjp_683_:
{
lean_object* v___x_687_; 
if (v_isShared_685_ == 0)
{
lean_ctor_set_tag(v___x_684_, 0);
v___x_687_ = v___x_684_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_688_; 
v_reuseFailAlloc_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_688_, 0, v_val_682_);
v___x_687_ = v_reuseFailAlloc_688_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
return v___x_687_;
}
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec_ref(v___x_681_);
v___x_690_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_691_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_690_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_700_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
if (lean_obj_tag(v_a_692_) == 0)
{
lean_del_object(v___x_694_);
goto v___jp_667_;
}
else
{
lean_object* v_val_696_; lean_object* v___x_698_; 
lean_dec(v_constName_661_);
v_val_696_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_val_696_);
lean_dec_ref_known(v_a_692_, 1);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v_val_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_val_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_708_; 
lean_dec(v_constName_661_);
v_a_701_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_708_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_708_ == 0)
{
v___x_703_ = v___x_691_;
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_691_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_708_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_706_; 
if (v_isShared_704_ == 0)
{
v___x_706_ = v___x_703_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
else
{
lean_dec(v_val_679_);
goto v___jp_667_;
}
}
else
{
lean_dec(v___x_678_);
goto v___jp_667_;
}
v___jp_667_:
{
lean_object* v___x_668_; uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_668_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_669_ = 0;
v___x_670_ = l_Lean_MessageData_ofConstName(v_constName_661_, v___x_669_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_668_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_673_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
return v___x_674_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_716_, lean_object* v___x_717_, lean_object* v_as_x27_718_, lean_object* v_b_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
if (lean_obj_tag(v_as_x27_718_) == 0)
{
lean_object* v___x_725_; 
v___x_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_725_, 0, v_b_719_);
return v___x_725_;
}
else
{
lean_object* v_head_726_; lean_object* v_tail_727_; lean_object* v___x_728_; 
v_head_726_ = lean_ctor_get(v_as_x27_718_, 0);
v_tail_727_ = lean_ctor_get(v_as_x27_718_, 1);
lean_inc(v_head_726_);
v___x_728_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_726_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v_toConstantVal_730_; lean_object* v_cidx_731_; lean_object* v_numFields_732_; lean_object* v_type_733_; lean_object* v___x_734_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v_toConstantVal_730_ = lean_ctor_get(v_a_729_, 0);
lean_inc_ref(v_toConstantVal_730_);
v_cidx_731_ = lean_ctor_get(v_a_729_, 2);
lean_inc(v_cidx_731_);
v_numFields_732_ = lean_ctor_get(v_a_729_, 4);
lean_inc(v_numFields_732_);
lean_dec(v_a_729_);
v_type_733_ = lean_ctor_get(v_toConstantVal_730_, 2);
lean_inc_ref(v_type_733_);
lean_dec_ref(v_toConstantVal_730_);
v___x_734_ = l_Lean_Meta_instantiateForall(v_type_733_, v___x_717_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_752_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_752_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_752_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_752_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
uint8_t v___x_739_; uint8_t v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___f_744_; lean_object* v___x_746_; 
v___x_739_ = 0;
v___x_740_ = 1;
v___x_741_ = lean_box(v___x_739_);
v___x_742_ = lean_box(v___x_716_);
v___x_743_ = lean_box(v___x_740_);
v___f_744_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_744_, 0, v_cidx_731_);
lean_closure_set(v___f_744_, 1, v___x_741_);
lean_closure_set(v___f_744_, 2, v___x_742_);
lean_closure_set(v___f_744_, 3, v___x_743_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 1);
lean_ctor_set(v___x_737_, 0, v_numFields_732_);
v___x_746_ = v___x_737_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_numFields_732_);
v___x_746_ = v_reuseFailAlloc_751_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_735_, v___x_746_, v___f_744_, v___x_739_, v___x_739_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_749_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
lean_inc(v_a_748_);
lean_dec_ref_known(v___x_747_, 1);
v___x_749_ = l_Lean_Expr_app___override(v_b_719_, v_a_748_);
v_as_x27_718_ = v_tail_727_;
v_b_719_ = v___x_749_;
goto _start;
}
else
{
lean_dec_ref(v_b_719_);
return v___x_747_;
}
}
}
}
else
{
lean_dec(v_numFields_732_);
lean_dec(v_cidx_731_);
lean_dec_ref(v_b_719_);
return v___x_734_;
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v_b_719_);
v_a_753_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_728_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_728_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_761_, lean_object* v___x_762_, lean_object* v_as_x27_763_, lean_object* v_b_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
uint8_t v___x_34901__boxed_770_; lean_object* v_res_771_; 
v___x_34901__boxed_770_ = lean_unbox(v___x_761_);
v_res_771_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_34901__boxed_770_, v___x_762_, v_as_x27_763_, v_b_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v_as_x27_763_);
lean_dec_ref(v___x_762_);
return v_res_771_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = lean_box(0);
v___x_773_ = l_Lean_Level_succ___override(v___x_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_774_, uint8_t v___x_775_, uint8_t v___x_776_, uint8_t v___x_777_, lean_object* v_val_778_, lean_object* v___x_779_, lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v___x_782_, lean_object* v___x_783_, lean_object* v_ctors_784_, lean_object* v___x_785_, lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_value_793_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_796_ = l_Lean_InductiveVal_numCtors(v_val_778_);
v___x_797_ = lean_unsigned_to_nat(1u);
v___x_798_ = lean_nat_dec_eq(v___x_796_, v___x_797_);
lean_dec(v___x_796_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v___x_785_);
lean_inc_ref(v_x_786_);
lean_inc_ref(v___x_779_);
v___x_799_ = lean_array_push(v___x_779_, v_x_786_);
v___x_800_ = l_Lean_Meta_mkLambdaFVars(v___x_799_, v___x_780_, v___x_775_, v___x_776_, v___x_775_, v___x_776_, v___x_777_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec_ref(v___x_799_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_801_);
lean_dec_ref_known(v___x_800_, 1);
v___x_802_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v___x_781_);
v___x_804_ = l_Lean_mkConst(v___x_782_, v___x_803_);
v___x_805_ = l_Lean_mkAppN(v___x_804_, v___x_783_);
v___x_806_ = l_Lean_Expr_app___override(v___x_805_, v_a_801_);
v___x_807_ = l_Lean_mkAppN(v___x_806_, v___x_779_);
lean_dec_ref(v___x_779_);
lean_inc_ref(v_x_786_);
v___x_808_ = l_Lean_Expr_app___override(v___x_807_, v_x_786_);
v___x_809_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_776_, v___x_783_, v_ctors_784_, v___x_808_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_809_, 1);
v_value_793_ = v_a_810_;
goto v___jp_792_;
}
else
{
lean_dec_ref(v_x_786_);
lean_dec_ref(v_xs_774_);
return v___x_809_;
}
}
else
{
lean_dec_ref(v_x_786_);
lean_dec(v___x_782_);
lean_dec(v___x_781_);
lean_dec_ref(v___x_779_);
lean_dec_ref(v_xs_774_);
return v___x_800_;
}
}
else
{
lean_object* v___x_811_; 
lean_dec(v___x_782_);
lean_dec(v___x_781_);
lean_dec_ref(v___x_780_);
lean_dec_ref(v___x_779_);
v___x_811_ = l_Lean_mkRawNatLit(v___x_785_);
v_value_793_ = v___x_811_;
goto v___jp_792_;
}
v___jp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_array_push(v_xs_774_, v_x_786_);
v___x_795_ = l_Lean_Meta_mkLambdaFVars(v___x_794_, v_value_793_, v___x_775_, v___x_776_, v___x_775_, v___x_776_, v___x_777_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
lean_dec_ref(v___x_794_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_812_ = _args[0];
lean_object* v___x_813_ = _args[1];
lean_object* v___x_814_ = _args[2];
lean_object* v___x_815_ = _args[3];
lean_object* v_val_816_ = _args[4];
lean_object* v___x_817_ = _args[5];
lean_object* v___x_818_ = _args[6];
lean_object* v___x_819_ = _args[7];
lean_object* v___x_820_ = _args[8];
lean_object* v___x_821_ = _args[9];
lean_object* v_ctors_822_ = _args[10];
lean_object* v___x_823_ = _args[11];
lean_object* v_x_824_ = _args[12];
lean_object* v___y_825_ = _args[13];
lean_object* v___y_826_ = _args[14];
lean_object* v___y_827_ = _args[15];
lean_object* v___y_828_ = _args[16];
lean_object* v___y_829_ = _args[17];
_start:
{
uint8_t v___x_34992__boxed_830_; uint8_t v___x_34993__boxed_831_; uint8_t v___x_34994__boxed_832_; lean_object* v_res_833_; 
v___x_34992__boxed_830_ = lean_unbox(v___x_813_);
v___x_34993__boxed_831_ = lean_unbox(v___x_814_);
v___x_34994__boxed_832_ = lean_unbox(v___x_815_);
v_res_833_ = l_Lean_mkCtorIdx___lam__0(v_xs_812_, v___x_34992__boxed_830_, v___x_34993__boxed_831_, v___x_34994__boxed_832_, v_val_816_, v___x_817_, v___x_818_, v___x_819_, v___x_820_, v___x_821_, v_ctors_822_, v___x_823_, v_x_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_ctors_822_);
lean_dec_ref(v___x_821_);
lean_dec_ref(v_val_816_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v___x_841_; 
lean_inc(v___y_839_);
lean_inc_ref(v___y_838_);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
v___x_841_ = lean_apply_6(v_k_834_, v_b_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, lean_box(0));
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_842_, lean_object* v_b_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_842_, v_b_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_850_, uint8_t v_bi_851_, lean_object* v_type_852_, lean_object* v_k_853_, uint8_t v_kind_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___f_860_; lean_object* v___x_861_; 
v___f_860_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_860_, 0, v_k_853_);
v___x_861_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_850_, v_bi_851_, v_type_852_, v___f_860_, v_kind_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_861_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_861_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
v_a_870_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_861_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_861_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_878_, lean_object* v_bi_879_, lean_object* v_type_880_, lean_object* v_k_881_, lean_object* v_kind_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v_bi_boxed_888_; uint8_t v_kind_boxed_889_; lean_object* v_res_890_; 
v_bi_boxed_888_ = lean_unbox(v_bi_879_);
v_kind_boxed_889_ = lean_unbox(v_kind_882_);
v_res_890_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_878_, v_bi_boxed_888_, v_type_880_, v_k_881_, v_kind_boxed_889_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_891_, lean_object* v_type_892_, lean_object* v_k_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
uint8_t v___x_899_; uint8_t v___x_900_; lean_object* v___x_901_; 
v___x_899_ = 0;
v___x_900_ = 0;
v___x_901_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_891_, v___x_899_, v_type_892_, v_k_893_, v___x_900_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_902_, lean_object* v_type_903_, lean_object* v_k_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_902_, v_type_903_, v_k_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(lean_object* v_declName_911_, uint8_t v_s_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; lean_object* v_env_917_; lean_object* v_nextMacroScope_918_; lean_object* v_ngen_919_; lean_object* v_auxDeclNGen_920_; lean_object* v_traceState_921_; lean_object* v_messages_922_; lean_object* v_infoState_923_; lean_object* v_snapshotTasks_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_953_; 
v___x_916_ = lean_st_ref_take(v___y_914_);
v_env_917_ = lean_ctor_get(v___x_916_, 0);
v_nextMacroScope_918_ = lean_ctor_get(v___x_916_, 1);
v_ngen_919_ = lean_ctor_get(v___x_916_, 2);
v_auxDeclNGen_920_ = lean_ctor_get(v___x_916_, 3);
v_traceState_921_ = lean_ctor_get(v___x_916_, 4);
v_messages_922_ = lean_ctor_get(v___x_916_, 6);
v_infoState_923_ = lean_ctor_get(v___x_916_, 7);
v_snapshotTasks_924_ = lean_ctor_get(v___x_916_, 8);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v___x_916_, 5);
lean_dec(v_unused_954_);
v___x_926_ = v___x_916_;
v_isShared_927_ = v_isSharedCheck_953_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_snapshotTasks_924_);
lean_inc(v_infoState_923_);
lean_inc(v_messages_922_);
lean_inc(v_traceState_921_);
lean_inc(v_auxDeclNGen_920_);
lean_inc(v_ngen_919_);
lean_inc(v_nextMacroScope_918_);
lean_inc(v_env_917_);
lean_dec(v___x_916_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_953_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
uint8_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_928_ = 0;
v___x_929_ = lean_box(0);
v___x_930_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_917_, v_declName_911_, v_s_912_, v___x_928_, v___x_929_);
v___x_931_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 5, v___x_931_);
lean_ctor_set(v___x_926_, 0, v___x_930_);
v___x_933_ = v___x_926_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_930_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_nextMacroScope_918_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_ngen_919_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_auxDeclNGen_920_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_traceState_921_);
lean_ctor_set(v_reuseFailAlloc_952_, 5, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_952_, 6, v_messages_922_);
lean_ctor_set(v_reuseFailAlloc_952_, 7, v_infoState_923_);
lean_ctor_set(v_reuseFailAlloc_952_, 8, v_snapshotTasks_924_);
v___x_933_ = v_reuseFailAlloc_952_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_mctx_936_; lean_object* v_zetaDeltaFVarIds_937_; lean_object* v_postponed_938_; lean_object* v_diag_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_950_; 
v___x_934_ = lean_st_ref_set(v___y_914_, v___x_933_);
v___x_935_ = lean_st_ref_take(v___y_913_);
v_mctx_936_ = lean_ctor_get(v___x_935_, 0);
v_zetaDeltaFVarIds_937_ = lean_ctor_get(v___x_935_, 2);
v_postponed_938_ = lean_ctor_get(v___x_935_, 3);
v_diag_939_ = lean_ctor_get(v___x_935_, 4);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_935_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v___x_935_, 1);
lean_dec(v_unused_951_);
v___x_941_ = v___x_935_;
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_diag_939_);
lean_inc(v_postponed_938_);
lean_inc(v_zetaDeltaFVarIds_937_);
lean_inc(v_mctx_936_);
lean_dec(v___x_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_950_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_mctx_936_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_949_, 2, v_zetaDeltaFVarIds_937_);
lean_ctor_set(v_reuseFailAlloc_949_, 3, v_postponed_938_);
lean_ctor_set(v_reuseFailAlloc_949_, 4, v_diag_939_);
v___x_945_ = v_reuseFailAlloc_949_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_946_ = lean_st_ref_set(v___y_913_, v___x_945_);
v___x_947_ = lean_box(0);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v___x_947_);
return v___x_948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object* v_declName_955_, lean_object* v_s_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
uint8_t v_s_boxed_960_; lean_object* v_res_961_; 
v_s_boxed_960_ = lean_unbox(v_s_956_);
v_res_961_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(v_declName_955_, v_s_boxed_960_, v___y_957_, v___y_958_);
lean_dec(v___y_958_);
lean_dec(v___y_957_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(lean_object* v_declName_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_){
_start:
{
uint8_t v___x_968_; lean_object* v___x_969_; 
v___x_968_ = 0;
v___x_969_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(v_declName_962_, v___x_968_, v___y_964_, v___y_966_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_declName_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(v_declName_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_976_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_977_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
v___x_979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
lean_ctor_set(v___x_982_, 2, v___x_981_);
lean_ctor_set(v___x_982_, 3, v___x_981_);
lean_ctor_set(v___x_982_, 4, v___x_980_);
lean_ctor_set(v___x_982_, 5, v___x_980_);
lean_ctor_set(v___x_982_, 6, v___x_980_);
lean_ctor_set(v___x_982_, 7, v___x_980_);
lean_ctor_set(v___x_982_, 8, v___x_980_);
lean_ctor_set(v___x_982_, 9, v___x_980_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_983_ = lean_unsigned_to_nat(32u);
v___x_984_ = lean_mk_empty_array_with_capacity(v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_986_ = ((size_t)5ULL);
v___x_987_ = lean_unsigned_to_nat(0u);
v___x_988_ = lean_unsigned_to_nat(32u);
v___x_989_ = lean_mk_empty_array_with_capacity(v___x_988_);
v___x_990_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
v___x_991_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_991_, 0, v___x_990_);
lean_ctor_set(v___x_991_, 1, v___x_989_);
lean_ctor_set(v___x_991_, 2, v___x_987_);
lean_ctor_set(v___x_991_, 3, v___x_987_);
lean_ctor_set_usize(v___x_991_, 4, v___x_986_);
return v___x_991_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_992_ = lean_box(1);
v___x_993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
v___x_994_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v___x_993_);
lean_ctor_set(v___x_995_, 2, v___x_992_);
return v___x_995_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6));
v___x_998_ = l_Lean_stringToMessageData(v___x_997_);
return v___x_998_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8));
v___x_1001_ = l_Lean_stringToMessageData(v___x_1000_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10));
v___x_1004_ = l_Lean_stringToMessageData(v___x_1003_);
return v___x_1004_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12));
v___x_1007_ = l_Lean_stringToMessageData(v___x_1006_);
return v___x_1007_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14));
v___x_1010_ = l_Lean_stringToMessageData(v___x_1009_);
return v___x_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16));
v___x_1013_ = l_Lean_stringToMessageData(v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1015_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18));
v___x_1016_ = l_Lean_stringToMessageData(v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object* v_msg_1017_, lean_object* v_declHint_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v_env_1022_; uint8_t v___y_1024_; uint8_t v___x_1080_; uint8_t v___x_1081_; 
v___x_1021_ = lean_st_ref_get(v___y_1019_);
v_env_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc_ref(v_env_1022_);
lean_dec(v___x_1021_);
v___x_1080_ = l_Lean_Name_isAnonymous(v_declHint_1018_);
v___x_1081_ = lean_bool_not(v___x_1080_);
if (v___x_1081_ == 0)
{
v___y_1024_ = v___x_1081_;
goto v___jp_1023_;
}
else
{
uint8_t v_isExporting_1082_; 
v_isExporting_1082_ = lean_ctor_get_uint8(v_env_1022_, sizeof(void*)*8);
v___y_1024_ = v_isExporting_1082_;
goto v___jp_1023_;
}
v___jp_1023_:
{
if (v___y_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec_ref(v_env_1022_);
lean_dec(v_declHint_1018_);
v___x_1025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1025_, 0, v_msg_1017_);
return v___x_1025_;
}
else
{
uint8_t v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1026_ = 0;
lean_inc_ref(v_env_1022_);
v___x_1027_ = l_Lean_Environment_setExporting(v_env_1022_, v___x_1026_);
lean_inc(v_declHint_1018_);
lean_inc_ref(v___x_1027_);
v___x_1028_ = l_Lean_Environment_contains(v___x_1027_, v_declHint_1018_, v___y_1024_);
if (v___x_1028_ == 0)
{
lean_object* v___x_1029_; 
lean_dec_ref(v___x_1027_);
lean_dec_ref(v_env_1022_);
lean_dec(v_declHint_1018_);
v___x_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1029_, 0, v_msg_1017_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v_c_1035_; lean_object* v___x_1036_; 
v___x_1030_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
v___x_1031_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
v___x_1032_ = l_Lean_Options_empty;
v___x_1033_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1027_);
lean_ctor_set(v___x_1033_, 1, v___x_1030_);
lean_ctor_set(v___x_1033_, 2, v___x_1031_);
lean_ctor_set(v___x_1033_, 3, v___x_1032_);
lean_inc(v_declHint_1018_);
v___x_1034_ = l_Lean_MessageData_ofConstName(v_declHint_1018_, v___x_1026_);
v_c_1035_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1035_, 0, v___x_1033_);
lean_ctor_set(v_c_1035_, 1, v___x_1034_);
v___x_1036_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1022_, v_declHint_1018_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
lean_dec_ref(v_env_1022_);
lean_dec(v_declHint_1018_);
v___x_1037_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_c_1035_);
v___x_1039_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
v___x_1040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1038_);
lean_ctor_set(v___x_1040_, 1, v___x_1039_);
v___x_1041_ = l_Lean_MessageData_note(v___x_1040_);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v_msg_1017_);
lean_ctor_set(v___x_1042_, 1, v___x_1041_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
return v___x_1043_;
}
else
{
lean_object* v_val_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1079_; 
v_val_1044_ = lean_ctor_get(v___x_1036_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1046_ = v___x_1036_;
v_isShared_1047_ = v_isSharedCheck_1079_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_val_1044_);
lean_dec(v___x_1036_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1079_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_mod_1051_; uint8_t v___x_1052_; 
v___x_1048_ = lean_box(0);
v___x_1049_ = l_Lean_Environment_header(v_env_1022_);
lean_dec_ref(v_env_1022_);
v___x_1050_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1049_);
v_mod_1051_ = lean_array_get(v___x_1048_, v___x_1050_, v_val_1044_);
lean_dec(v_val_1044_);
lean_dec_ref(v___x_1050_);
v___x_1052_ = l_Lean_isPrivateName(v_declHint_1018_);
lean_dec(v_declHint_1018_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1064_; 
v___x_1053_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
v___x_1054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_c_1035_);
v___x_1055_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
v___x_1056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1054_);
lean_ctor_set(v___x_1056_, 1, v___x_1055_);
v___x_1057_ = l_Lean_MessageData_ofName(v_mod_1051_);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1056_);
lean_ctor_set(v___x_1058_, 1, v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_MessageData_note(v___x_1060_);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v_msg_1017_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1062_);
v___x_1064_ = v___x_1046_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v___x_1066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_1067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
lean_ctor_set(v___x_1067_, 1, v_c_1035_);
v___x_1068_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
v___x_1069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1067_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_MessageData_ofName(v_mod_1051_);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1069_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
v___x_1072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_MessageData_note(v___x_1073_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_msg_1017_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set_tag(v___x_1046_, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1075_);
v___x_1077_ = v___x_1046_;
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
return v___x_1077_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object* v_msg_1083_, lean_object* v_declHint_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_1083_, v_declHint_1084_, v___y_1085_);
lean_dec(v___y_1085_);
return v_res_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object* v_msg_1088_, lean_object* v_declHint_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_){
_start:
{
lean_object* v___x_1095_; lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1105_; 
v___x_1095_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_1088_, v_declHint_1089_, v___y_1093_);
v_a_1096_ = lean_ctor_get(v___x_1095_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1095_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1098_ = v___x_1095_;
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1095_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1105_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v___x_1100_ = l_Lean_unknownIdentifierMessageTag;
v___x_1101_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1100_);
lean_ctor_set(v___x_1101_, 1, v_a_1096_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 0, v___x_1101_);
v___x_1103_ = v___x_1098_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object* v_msg_1106_, lean_object* v_declHint_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_res_1113_; 
v_res_1113_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_1106_, v_declHint_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
lean_dec(v___y_1111_);
lean_dec_ref(v___y_1110_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
return v_res_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object* v_ref_1114_, lean_object* v_msg_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_){
_start:
{
lean_object* v_fileName_1121_; lean_object* v_fileMap_1122_; lean_object* v_options_1123_; lean_object* v_currRecDepth_1124_; lean_object* v_maxRecDepth_1125_; lean_object* v_ref_1126_; lean_object* v_currNamespace_1127_; lean_object* v_openDecls_1128_; lean_object* v_initHeartbeats_1129_; lean_object* v_maxHeartbeats_1130_; lean_object* v_quotContext_1131_; lean_object* v_currMacroScope_1132_; uint8_t v_diag_1133_; lean_object* v_cancelTk_x3f_1134_; uint8_t v_suppressElabErrors_1135_; lean_object* v_inheritedTraceOptions_1136_; lean_object* v_ref_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v_fileName_1121_ = lean_ctor_get(v___y_1118_, 0);
v_fileMap_1122_ = lean_ctor_get(v___y_1118_, 1);
v_options_1123_ = lean_ctor_get(v___y_1118_, 2);
v_currRecDepth_1124_ = lean_ctor_get(v___y_1118_, 3);
v_maxRecDepth_1125_ = lean_ctor_get(v___y_1118_, 4);
v_ref_1126_ = lean_ctor_get(v___y_1118_, 5);
v_currNamespace_1127_ = lean_ctor_get(v___y_1118_, 6);
v_openDecls_1128_ = lean_ctor_get(v___y_1118_, 7);
v_initHeartbeats_1129_ = lean_ctor_get(v___y_1118_, 8);
v_maxHeartbeats_1130_ = lean_ctor_get(v___y_1118_, 9);
v_quotContext_1131_ = lean_ctor_get(v___y_1118_, 10);
v_currMacroScope_1132_ = lean_ctor_get(v___y_1118_, 11);
v_diag_1133_ = lean_ctor_get_uint8(v___y_1118_, sizeof(void*)*14);
v_cancelTk_x3f_1134_ = lean_ctor_get(v___y_1118_, 12);
v_suppressElabErrors_1135_ = lean_ctor_get_uint8(v___y_1118_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1136_ = lean_ctor_get(v___y_1118_, 13);
v_ref_1137_ = l_Lean_replaceRef(v_ref_1114_, v_ref_1126_);
lean_inc_ref(v_inheritedTraceOptions_1136_);
lean_inc(v_cancelTk_x3f_1134_);
lean_inc(v_currMacroScope_1132_);
lean_inc(v_quotContext_1131_);
lean_inc(v_maxHeartbeats_1130_);
lean_inc(v_initHeartbeats_1129_);
lean_inc(v_openDecls_1128_);
lean_inc(v_currNamespace_1127_);
lean_inc(v_maxRecDepth_1125_);
lean_inc(v_currRecDepth_1124_);
lean_inc_ref(v_options_1123_);
lean_inc_ref(v_fileMap_1122_);
lean_inc_ref(v_fileName_1121_);
v___x_1138_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1138_, 0, v_fileName_1121_);
lean_ctor_set(v___x_1138_, 1, v_fileMap_1122_);
lean_ctor_set(v___x_1138_, 2, v_options_1123_);
lean_ctor_set(v___x_1138_, 3, v_currRecDepth_1124_);
lean_ctor_set(v___x_1138_, 4, v_maxRecDepth_1125_);
lean_ctor_set(v___x_1138_, 5, v_ref_1137_);
lean_ctor_set(v___x_1138_, 6, v_currNamespace_1127_);
lean_ctor_set(v___x_1138_, 7, v_openDecls_1128_);
lean_ctor_set(v___x_1138_, 8, v_initHeartbeats_1129_);
lean_ctor_set(v___x_1138_, 9, v_maxHeartbeats_1130_);
lean_ctor_set(v___x_1138_, 10, v_quotContext_1131_);
lean_ctor_set(v___x_1138_, 11, v_currMacroScope_1132_);
lean_ctor_set(v___x_1138_, 12, v_cancelTk_x3f_1134_);
lean_ctor_set(v___x_1138_, 13, v_inheritedTraceOptions_1136_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*14, v_diag_1133_);
lean_ctor_set_uint8(v___x_1138_, sizeof(void*)*14 + 1, v_suppressElabErrors_1135_);
v___x_1139_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1115_, v___y_1116_, v___y_1117_, v___x_1138_, v___y_1119_);
lean_dec_ref_known(v___x_1138_, 14);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object* v_ref_1140_, lean_object* v_msg_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_1140_, v_msg_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v_ref_1140_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object* v_ref_1148_, lean_object* v_msg_1149_, lean_object* v_declHint_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1156_; lean_object* v_a_1157_; lean_object* v___x_1158_; 
v___x_1156_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_1149_, v_declHint_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref(v___x_1156_);
v___x_1158_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_1148_, v_a_1157_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1159_, lean_object* v_msg_1160_, lean_object* v_declHint_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1159_, v_msg_1160_, v_declHint_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1164_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1162_);
lean_dec(v_ref_1159_);
return v_res_1167_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1170_ = l_Lean_stringToMessageData(v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1171_, lean_object* v_constName_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1178_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1179_ = 0;
lean_inc(v_constName_1172_);
v___x_1180_ = l_Lean_MessageData_ofConstName(v_constName_1172_, v___x_1179_);
v___x_1181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1178_);
lean_ctor_set(v___x_1181_, 1, v___x_1180_);
v___x_1182_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1181_);
lean_ctor_set(v___x_1183_, 1, v___x_1182_);
v___x_1184_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1171_, v___x_1183_, v_constName_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1185_, lean_object* v_constName_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1185_, v_constName_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v_ref_1185_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_){
_start:
{
lean_object* v_ref_1199_; lean_object* v___x_1200_; 
v_ref_1199_ = lean_ctor_get(v___y_1196_, 5);
v___x_1200_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1199_, v_constName_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_){
_start:
{
lean_object* v___x_1214_; lean_object* v_env_1215_; uint8_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1214_ = lean_st_ref_get(v___y_1212_);
v_env_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc_ref(v_env_1215_);
lean_dec(v___x_1214_);
v___x_1216_ = 0;
lean_inc(v_constName_1208_);
v___x_1217_ = l_Lean_Environment_find_x3f(v_env_1215_, v_constName_1208_, v___x_1216_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_);
return v___x_1218_;
}
else
{
lean_object* v_val_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1226_; 
lean_dec(v_constName_1208_);
v_val_1219_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1226_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1221_ = v___x_1217_;
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_val_1219_);
lean_dec(v___x_1217_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1226_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v___x_1224_; 
if (v_isShared_1222_ == 0)
{
lean_ctor_set_tag(v___x_1221_, 0);
v___x_1224_ = v___x_1221_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_val_1219_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(lean_object* v_x_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
if (lean_obj_tag(v_x_1234_) == 0)
{
uint8_t v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = 1;
v___x_1241_ = lean_box(v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
return v___x_1242_;
}
else
{
lean_object* v_head_1243_; lean_object* v_tail_1244_; lean_object* v___x_1245_; 
v_head_1243_ = lean_ctor_get(v_x_1234_, 0);
lean_inc(v_head_1243_);
v_tail_1244_ = lean_ctor_get(v_x_1234_, 1);
lean_inc(v_tail_1244_);
lean_dec_ref_known(v_x_1234_, 2);
v___x_1245_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_head_1243_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1264_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1248_ = v___x_1245_;
v_isShared_1249_ = v_isSharedCheck_1264_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1245_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1264_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
if (lean_obj_tag(v_a_1246_) == 6)
{
lean_object* v_val_1250_; lean_object* v_numFields_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; 
v_val_1250_ = lean_ctor_get(v_a_1246_, 0);
lean_inc_ref(v_val_1250_);
lean_dec_ref_known(v_a_1246_, 1);
v_numFields_1251_ = lean_ctor_get(v_val_1250_, 4);
lean_inc(v_numFields_1251_);
lean_dec_ref(v_val_1250_);
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_nat_dec_eq(v_numFields_1251_, v___x_1252_);
lean_dec(v_numFields_1251_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
lean_dec(v_tail_1244_);
v___x_1254_ = lean_box(v___x_1253_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1254_);
v___x_1256_ = v___x_1248_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_del_object(v___x_1248_);
v_x_1234_ = v_tail_1244_;
goto _start;
}
}
else
{
uint8_t v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_dec(v_a_1246_);
lean_dec(v_tail_1244_);
v___x_1259_ = 0;
v___x_1260_ = lean_box(v___x_1259_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v___x_1260_);
v___x_1262_ = v___x_1248_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
else
{
lean_object* v_a_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1272_; 
lean_dec(v_tail_1244_);
v_a_1265_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1272_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1267_ = v___x_1245_;
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_a_1265_);
lean_dec(v___x_1245_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1272_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1265_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v_x_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(v_x_1273_, v___y_1274_, v___y_1275_, v___y_1276_, v___y_1277_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(lean_object* v_declName_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_declName_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1343_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1343_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1343_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
if (lean_obj_tag(v_a_1287_) == 5)
{
lean_object* v_val_1291_; lean_object* v_toConstantVal_1292_; lean_object* v_numParams_1293_; lean_object* v_numIndices_1294_; lean_object* v_ctors_1295_; uint8_t v_isRec_1296_; uint8_t v_isUnsafe_1297_; uint8_t v___y_1299_; lean_object* v_type_1332_; uint8_t v___x_1333_; uint8_t v___x_1334_; 
v_val_1291_ = lean_ctor_get(v_a_1287_, 0);
lean_inc_ref(v_val_1291_);
lean_dec_ref_known(v_a_1287_, 1);
v_toConstantVal_1292_ = lean_ctor_get(v_val_1291_, 0);
v_numParams_1293_ = lean_ctor_get(v_val_1291_, 1);
lean_inc(v_numParams_1293_);
v_numIndices_1294_ = lean_ctor_get(v_val_1291_, 2);
lean_inc(v_numIndices_1294_);
v_ctors_1295_ = lean_ctor_get(v_val_1291_, 4);
lean_inc(v_ctors_1295_);
v_isRec_1296_ = lean_ctor_get_uint8(v_val_1291_, sizeof(void*)*6);
v_isUnsafe_1297_ = lean_ctor_get_uint8(v_val_1291_, sizeof(void*)*6 + 1);
v_type_1332_ = lean_ctor_get(v_toConstantVal_1292_, 2);
v___x_1333_ = l_Lean_Expr_isProp(v_type_1332_);
v___x_1334_ = lean_bool_not(v___x_1333_);
if (v___x_1334_ == 0)
{
lean_dec_ref(v_val_1291_);
v___y_1299_ = v___x_1334_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = l_Lean_InductiveVal_numTypeFormers(v_val_1291_);
lean_dec_ref(v_val_1291_);
v___x_1336_ = lean_unsigned_to_nat(1u);
v___x_1337_ = lean_nat_dec_eq(v___x_1335_, v___x_1336_);
lean_dec(v___x_1335_);
v___y_1299_ = v___x_1337_;
goto v___jp_1298_;
}
v___jp_1298_:
{
if (v___y_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1302_; 
lean_dec(v_ctors_1295_);
lean_dec(v_numIndices_1294_);
lean_dec(v_numParams_1293_);
v___x_1300_ = lean_box(v___y_1299_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1300_);
v___x_1302_ = v___x_1289_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
else
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_nat_dec_eq(v_numIndices_1294_, v___x_1304_);
lean_dec(v_numIndices_1294_);
if (v___x_1305_ == 0)
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
lean_dec(v_ctors_1295_);
lean_dec(v_numParams_1293_);
v___x_1306_ = lean_box(v___x_1305_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1306_);
v___x_1308_ = v___x_1289_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
else
{
uint8_t v___x_1310_; 
v___x_1310_ = lean_nat_dec_eq(v_numParams_1293_, v___x_1304_);
lean_dec(v_numParams_1293_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
lean_dec(v_ctors_1295_);
v___x_1311_ = lean_box(v___x_1310_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1311_);
v___x_1313_ = v___x_1289_;
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
else
{
uint8_t v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = l_List_isEmpty___redArg(v_ctors_1295_);
v___x_1316_ = lean_bool_not(v___x_1315_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
lean_dec(v_ctors_1295_);
v___x_1317_ = lean_box(v___x_1316_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1317_);
v___x_1319_ = v___x_1289_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
else
{
uint8_t v___x_1321_; 
v___x_1321_ = lean_bool_not(v_isRec_1296_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_dec(v_ctors_1295_);
v___x_1322_ = lean_box(v___x_1321_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1322_);
v___x_1324_ = v___x_1289_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1322_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
else
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_bool_not(v_isUnsafe_1297_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
lean_dec(v_ctors_1295_);
v___x_1327_ = lean_box(v___x_1326_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1327_);
v___x_1329_ = v___x_1289_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
else
{
lean_object* v___x_1331_; 
lean_del_object(v___x_1289_);
v___x_1331_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(v_ctors_1295_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1331_;
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
uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
lean_dec(v_a_1287_);
v___x_1338_ = 0;
v___x_1339_ = lean_box(v___x_1338_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1339_);
v___x_1341_ = v___x_1289_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
v_a_1344_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1286_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1286_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_declName_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(v_declName_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(lean_object* v_env_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v_nextMacroScope_1364_; lean_object* v_ngen_1365_; lean_object* v_auxDeclNGen_1366_; lean_object* v_traceState_1367_; lean_object* v_messages_1368_; lean_object* v_infoState_1369_; lean_object* v_snapshotTasks_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1396_; 
v___x_1363_ = lean_st_ref_take(v___y_1361_);
v_nextMacroScope_1364_ = lean_ctor_get(v___x_1363_, 1);
v_ngen_1365_ = lean_ctor_get(v___x_1363_, 2);
v_auxDeclNGen_1366_ = lean_ctor_get(v___x_1363_, 3);
v_traceState_1367_ = lean_ctor_get(v___x_1363_, 4);
v_messages_1368_ = lean_ctor_get(v___x_1363_, 6);
v_infoState_1369_ = lean_ctor_get(v___x_1363_, 7);
v_snapshotTasks_1370_ = lean_ctor_get(v___x_1363_, 8);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1396_ == 0)
{
lean_object* v_unused_1397_; lean_object* v_unused_1398_; 
v_unused_1397_ = lean_ctor_get(v___x_1363_, 5);
lean_dec(v_unused_1397_);
v_unused_1398_ = lean_ctor_get(v___x_1363_, 0);
lean_dec(v_unused_1398_);
v___x_1372_ = v___x_1363_;
v_isShared_1373_ = v_isSharedCheck_1396_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_snapshotTasks_1370_);
lean_inc(v_infoState_1369_);
lean_inc(v_messages_1368_);
lean_inc(v_traceState_1367_);
lean_inc(v_auxDeclNGen_1366_);
lean_inc(v_ngen_1365_);
lean_inc(v_nextMacroScope_1364_);
lean_dec(v___x_1363_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1396_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 5, v___x_1374_);
lean_ctor_set(v___x_1372_, 0, v_env_1359_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_env_1359_);
lean_ctor_set(v_reuseFailAlloc_1395_, 1, v_nextMacroScope_1364_);
lean_ctor_set(v_reuseFailAlloc_1395_, 2, v_ngen_1365_);
lean_ctor_set(v_reuseFailAlloc_1395_, 3, v_auxDeclNGen_1366_);
lean_ctor_set(v_reuseFailAlloc_1395_, 4, v_traceState_1367_);
lean_ctor_set(v_reuseFailAlloc_1395_, 5, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1395_, 6, v_messages_1368_);
lean_ctor_set(v_reuseFailAlloc_1395_, 7, v_infoState_1369_);
lean_ctor_set(v_reuseFailAlloc_1395_, 8, v_snapshotTasks_1370_);
v___x_1376_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v_mctx_1379_; lean_object* v_zetaDeltaFVarIds_1380_; lean_object* v_postponed_1381_; lean_object* v_diag_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1393_; 
v___x_1377_ = lean_st_ref_set(v___y_1361_, v___x_1376_);
v___x_1378_ = lean_st_ref_take(v___y_1360_);
v_mctx_1379_ = lean_ctor_get(v___x_1378_, 0);
v_zetaDeltaFVarIds_1380_ = lean_ctor_get(v___x_1378_, 2);
v_postponed_1381_ = lean_ctor_get(v___x_1378_, 3);
v_diag_1382_ = lean_ctor_get(v___x_1378_, 4);
v_isSharedCheck_1393_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1393_ == 0)
{
lean_object* v_unused_1394_; 
v_unused_1394_ = lean_ctor_get(v___x_1378_, 1);
lean_dec(v_unused_1394_);
v___x_1384_ = v___x_1378_;
v_isShared_1385_ = v_isSharedCheck_1393_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_diag_1382_);
lean_inc(v_postponed_1381_);
lean_inc(v_zetaDeltaFVarIds_1380_);
lean_inc(v_mctx_1379_);
lean_dec(v___x_1378_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1393_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1386_; lean_object* v___x_1388_; 
v___x_1386_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1385_ == 0)
{
lean_ctor_set(v___x_1384_, 1, v___x_1386_);
v___x_1388_ = v___x_1384_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1392_; 
v_reuseFailAlloc_1392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_mctx_1379_);
lean_ctor_set(v_reuseFailAlloc_1392_, 1, v___x_1386_);
lean_ctor_set(v_reuseFailAlloc_1392_, 2, v_zetaDeltaFVarIds_1380_);
lean_ctor_set(v_reuseFailAlloc_1392_, 3, v_postponed_1381_);
lean_ctor_set(v_reuseFailAlloc_1392_, 4, v_diag_1382_);
v___x_1388_ = v_reuseFailAlloc_1392_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_st_ref_set(v___y_1360_, v___x_1388_);
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object* v_env_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(v_env_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec(v___y_1400_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(lean_object* v_declName_1404_, lean_object* v_entry_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v_env_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1411_ = lean_st_ref_get(v___y_1409_);
v_env_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc_ref(v_env_1412_);
lean_dec(v___x_1411_);
v___x_1413_ = l_Lean_Linter_deprecatedAttr;
v___x_1414_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1413_, v_env_1412_, v_declName_1404_, v_entry_1405_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1424_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1414_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1417_ = v___x_1414_;
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1414_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1424_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
lean_ctor_set_tag(v___x_1417_, 3);
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1421_ = l_Lean_MessageData_ofFormat(v___x_1420_);
v___x_1422_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_1421_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
return v___x_1422_;
}
}
}
else
{
lean_object* v_a_1425_; lean_object* v___x_1426_; 
v_a_1425_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1425_);
lean_dec_ref_known(v___x_1414_, 1);
v___x_1426_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(v_a_1425_, v___y_1407_, v___y_1409_);
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object* v_declName_1427_, lean_object* v_entry_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(v_declName_1427_, v_entry_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_1441_, lean_object* v___x_1442_, lean_object* v_xs_1443_, uint8_t v___x_1444_, uint8_t v___x_1445_, lean_object* v_val_1446_, lean_object* v___x_1447_, lean_object* v___x_1448_, lean_object* v___x_1449_, lean_object* v___x_1450_, lean_object* v_ctors_1451_, lean_object* v___x_1452_, lean_object* v___x_1453_, lean_object* v_levelParams_1454_, lean_object* v_indName_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___x_1552_; 
lean_inc_ref(v___x_1442_);
lean_inc_ref(v___x_1441_);
v___x_1552_ = l_Lean_mkArrow(v___x_1441_, v___x_1442_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; uint8_t v___x_1554_; lean_object* v___x_1555_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref_known(v___x_1552_, 1);
v___x_1554_ = 1;
v___x_1555_ = l_Lean_Meta_mkForallFVars(v_xs_1443_, v_a_1553_, v___x_1444_, v___x_1445_, v___x_1445_, v___x_1554_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = lean_box(v___x_1444_);
v___x_1558_ = lean_box(v___x_1445_);
v___x_1559_ = lean_box(v___x_1554_);
lean_inc(v___x_1448_);
lean_inc_ref(v_val_1446_);
v___f_1560_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1560_, 0, v_xs_1443_);
lean_closure_set(v___f_1560_, 1, v___x_1557_);
lean_closure_set(v___f_1560_, 2, v___x_1558_);
lean_closure_set(v___f_1560_, 3, v___x_1559_);
lean_closure_set(v___f_1560_, 4, v_val_1446_);
lean_closure_set(v___f_1560_, 5, v___x_1447_);
lean_closure_set(v___f_1560_, 6, v___x_1442_);
lean_closure_set(v___f_1560_, 7, v___x_1448_);
lean_closure_set(v___f_1560_, 8, v___x_1449_);
lean_closure_set(v___f_1560_, 9, v___x_1450_);
lean_closure_set(v___f_1560_, 10, v_ctors_1451_);
lean_closure_set(v___f_1560_, 11, v___x_1452_);
v___x_1561_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__3));
v___x_1562_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_1561_, v___x_1441_, v___f_1560_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v_a_1563_; lean_object* v___x_1564_; lean_object* v_env_1565_; uint32_t v___x_1566_; uint32_t v___x_1567_; uint32_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1772_; 
v_a_1563_ = lean_ctor_get(v___x_1562_, 0);
lean_inc_n(v_a_1563_, 2);
lean_dec_ref_known(v___x_1562_, 1);
v___x_1564_ = lean_st_ref_get(v___y_1459_);
v_env_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc_ref(v_env_1565_);
lean_dec(v___x_1564_);
v___x_1566_ = l_Lean_getMaxHeight(v_env_1565_, v_a_1563_);
v___x_1567_ = 1;
v___x_1568_ = lean_uint32_add(v___x_1566_, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1569_, 0, v___x_1568_);
lean_inc(v_a_1556_);
lean_inc(v_levelParams_1454_);
lean_inc(v___x_1453_);
v___x_1570_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1453_, v_levelParams_1454_, v_a_1556_, v_a_1563_, v___x_1569_, v___y_1459_);
v_a_1571_ = lean_ctor_get(v___x_1570_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1570_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1573_ = v___x_1570_;
v_isShared_1574_ = v_isSharedCheck_1772_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1570_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1772_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 1);
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1581_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___y_1658_; lean_object* v___x_1697_; 
lean_inc_ref(v___x_1576_);
v___x_1697_ = l_Lean_addDecl(v___x_1576_, v___x_1444_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v___x_1698_; lean_object* v_env_1699_; lean_object* v_nextMacroScope_1700_; lean_object* v_ngen_1701_; lean_object* v_auxDeclNGen_1702_; lean_object* v_traceState_1703_; lean_object* v_messages_1704_; lean_object* v_infoState_1705_; lean_object* v_snapshotTasks_1706_; lean_object* v___x_1708_; uint8_t v_isShared_1709_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref_known(v___x_1697_, 1);
v___x_1698_ = lean_st_ref_take(v___y_1459_);
v_env_1699_ = lean_ctor_get(v___x_1698_, 0);
v_nextMacroScope_1700_ = lean_ctor_get(v___x_1698_, 1);
v_ngen_1701_ = lean_ctor_get(v___x_1698_, 2);
v_auxDeclNGen_1702_ = lean_ctor_get(v___x_1698_, 3);
v_traceState_1703_ = lean_ctor_get(v___x_1698_, 4);
v_messages_1704_ = lean_ctor_get(v___x_1698_, 6);
v_infoState_1705_ = lean_ctor_get(v___x_1698_, 7);
v_snapshotTasks_1706_ = lean_ctor_get(v___x_1698_, 8);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1698_);
if (v_isSharedCheck_1769_ == 0)
{
lean_object* v_unused_1770_; 
v_unused_1770_ = lean_ctor_get(v___x_1698_, 5);
lean_dec(v_unused_1770_);
v___x_1708_ = v___x_1698_;
v_isShared_1709_ = v_isSharedCheck_1769_;
goto v_resetjp_1707_;
}
else
{
lean_inc(v_snapshotTasks_1706_);
lean_inc(v_infoState_1705_);
lean_inc(v_messages_1704_);
lean_inc(v_traceState_1703_);
lean_inc(v_auxDeclNGen_1702_);
lean_inc(v_ngen_1701_);
lean_inc(v_nextMacroScope_1700_);
lean_inc(v_env_1699_);
lean_dec(v___x_1698_);
v___x_1708_ = lean_box(0);
v_isShared_1709_ = v_isSharedCheck_1769_;
goto v_resetjp_1707_;
}
v_resetjp_1707_:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
lean_inc(v___x_1453_);
v___x_1710_ = l_Lean_Meta_addToCompletionBlackList(v_env_1699_, v___x_1453_);
v___x_1711_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1709_ == 0)
{
lean_ctor_set(v___x_1708_, 5, v___x_1711_);
lean_ctor_set(v___x_1708_, 0, v___x_1710_);
v___x_1713_ = v___x_1708_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_nextMacroScope_1700_);
lean_ctor_set(v_reuseFailAlloc_1768_, 2, v_ngen_1701_);
lean_ctor_set(v_reuseFailAlloc_1768_, 3, v_auxDeclNGen_1702_);
lean_ctor_set(v_reuseFailAlloc_1768_, 4, v_traceState_1703_);
lean_ctor_set(v_reuseFailAlloc_1768_, 5, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1768_, 6, v_messages_1704_);
lean_ctor_set(v_reuseFailAlloc_1768_, 7, v_infoState_1705_);
lean_ctor_set(v_reuseFailAlloc_1768_, 8, v_snapshotTasks_1706_);
v___x_1713_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v_mctx_1716_; lean_object* v_zetaDeltaFVarIds_1717_; lean_object* v_postponed_1718_; lean_object* v_diag_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1766_; 
v___x_1714_ = lean_st_ref_set(v___y_1459_, v___x_1713_);
v___x_1715_ = lean_st_ref_take(v___y_1457_);
v_mctx_1716_ = lean_ctor_get(v___x_1715_, 0);
v_zetaDeltaFVarIds_1717_ = lean_ctor_get(v___x_1715_, 2);
v_postponed_1718_ = lean_ctor_get(v___x_1715_, 3);
v_diag_1719_ = lean_ctor_get(v___x_1715_, 4);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v___x_1715_, 1);
lean_dec(v_unused_1767_);
v___x_1721_ = v___x_1715_;
v_isShared_1722_ = v_isSharedCheck_1766_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_diag_1719_);
lean_inc(v_postponed_1718_);
lean_inc(v_zetaDeltaFVarIds_1717_);
lean_inc(v_mctx_1716_);
lean_dec(v___x_1715_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1766_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1723_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 1, v___x_1723_);
v___x_1725_ = v___x_1721_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_mctx_1716_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_zetaDeltaFVarIds_1717_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_postponed_1718_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_diag_1719_);
v___x_1725_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v_env_1728_; lean_object* v_nextMacroScope_1729_; lean_object* v_ngen_1730_; lean_object* v_auxDeclNGen_1731_; lean_object* v_traceState_1732_; lean_object* v_messages_1733_; lean_object* v_infoState_1734_; lean_object* v_snapshotTasks_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1763_; 
v___x_1726_ = lean_st_ref_set(v___y_1457_, v___x_1725_);
v___x_1727_ = lean_st_ref_take(v___y_1459_);
v_env_1728_ = lean_ctor_get(v___x_1727_, 0);
v_nextMacroScope_1729_ = lean_ctor_get(v___x_1727_, 1);
v_ngen_1730_ = lean_ctor_get(v___x_1727_, 2);
v_auxDeclNGen_1731_ = lean_ctor_get(v___x_1727_, 3);
v_traceState_1732_ = lean_ctor_get(v___x_1727_, 4);
v_messages_1733_ = lean_ctor_get(v___x_1727_, 6);
v_infoState_1734_ = lean_ctor_get(v___x_1727_, 7);
v_snapshotTasks_1735_ = lean_ctor_get(v___x_1727_, 8);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1763_ == 0)
{
lean_object* v_unused_1764_; 
v_unused_1764_ = lean_ctor_get(v___x_1727_, 5);
lean_dec(v_unused_1764_);
v___x_1737_ = v___x_1727_;
v_isShared_1738_ = v_isSharedCheck_1763_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_snapshotTasks_1735_);
lean_inc(v_infoState_1734_);
lean_inc(v_messages_1733_);
lean_inc(v_traceState_1732_);
lean_inc(v_auxDeclNGen_1731_);
lean_inc(v_ngen_1730_);
lean_inc(v_nextMacroScope_1729_);
lean_inc(v_env_1728_);
lean_dec(v___x_1727_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1763_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
lean_inc(v___x_1453_);
v___x_1739_ = l_Lean_addProtected(v_env_1728_, v___x_1453_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 5, v___x_1711_);
lean_ctor_set(v___x_1737_, 0, v___x_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_nextMacroScope_1729_);
lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_ngen_1730_);
lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_auxDeclNGen_1731_);
lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_traceState_1732_);
lean_ctor_set(v_reuseFailAlloc_1762_, 5, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1762_, 6, v_messages_1733_);
lean_ctor_set(v_reuseFailAlloc_1762_, 7, v_infoState_1734_);
lean_ctor_set(v_reuseFailAlloc_1762_, 8, v_snapshotTasks_1735_);
v___x_1741_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v_mctx_1744_; lean_object* v_zetaDeltaFVarIds_1745_; lean_object* v_postponed_1746_; lean_object* v_diag_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1760_; 
v___x_1742_ = lean_st_ref_set(v___y_1459_, v___x_1741_);
v___x_1743_ = lean_st_ref_take(v___y_1457_);
v_mctx_1744_ = lean_ctor_get(v___x_1743_, 0);
v_zetaDeltaFVarIds_1745_ = lean_ctor_get(v___x_1743_, 2);
v_postponed_1746_ = lean_ctor_get(v___x_1743_, 3);
v_diag_1747_ = lean_ctor_get(v___x_1743_, 4);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1743_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v___x_1743_, 1);
lean_dec(v_unused_1761_);
v___x_1749_ = v___x_1743_;
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_diag_1747_);
lean_inc(v_postponed_1746_);
lean_inc(v_zetaDeltaFVarIds_1745_);
lean_inc(v_mctx_1744_);
lean_dec(v___x_1743_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1760_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1723_);
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_mctx_1744_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_zetaDeltaFVarIds_1745_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_postponed_1746_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_diag_1747_);
v___x_1752_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1753_ = lean_st_ref_set(v___y_1457_, v___x_1752_);
v___x_1754_ = lean_unsigned_to_nat(1u);
v___x_1755_ = l_Lean_InductiveVal_numCtors(v_val_1446_);
lean_dec_ref(v_val_1446_);
v___x_1756_ = lean_nat_dec_eq(v___x_1755_, v___x_1754_);
lean_dec(v___x_1755_);
if (v___x_1756_ == 0)
{
v___y_1655_ = v___y_1456_;
v___y_1656_ = v___y_1457_;
v___y_1657_ = v___y_1458_;
v___y_1658_ = v___y_1459_;
goto v___jp_1654_;
}
else
{
uint8_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = 2;
lean_inc(v___x_1453_);
v___x_1758_ = l_Lean_Meta_setInlineAttribute(v___x_1453_, v___x_1757_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_dec_ref_known(v___x_1758_, 1);
v___y_1655_ = v___y_1456_;
v___y_1656_ = v___y_1457_;
v___y_1657_ = v___y_1458_;
v___y_1658_ = v___y_1459_;
goto v___jp_1654_;
}
else
{
lean_dec_ref(v___x_1576_);
lean_dec(v_a_1556_);
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1448_);
return v___x_1758_;
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
lean_dec_ref(v___x_1576_);
lean_dec(v_a_1556_);
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1448_);
lean_dec_ref(v_val_1446_);
return v___x_1697_;
}
v___jp_1577_:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Lean_compileDecl(v___x_1576_, v___x_1445_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref_known(v___x_1582_, 1);
lean_inc(v___x_1453_);
v___x_1583_ = l_Lean_enableRealizationsForConst(v___x_1453_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v___x_1584_; 
lean_dec_ref_known(v___x_1583_, 1);
lean_inc(v_indName_1455_);
v___x_1584_ = l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(v_indName_1455_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1645_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1587_ = v___x_1584_;
v_isShared_1588_ = v_isSharedCheck_1645_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1584_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1645_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
uint8_t v___x_1589_; 
v___x_1589_ = lean_unbox(v_a_1585_);
lean_dec(v_a_1585_);
if (v___x_1589_ == 0)
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
lean_dec(v_a_1556_);
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1448_);
v___x_1590_ = lean_box(0);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1590_);
v___x_1592_ = v___x_1587_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v_a_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1644_; 
lean_del_object(v___x_1587_);
lean_inc(v_indName_1455_);
v___x_1594_ = l_Lean_mkToCtorIdxName(v_indName_1455_);
lean_inc(v___x_1453_);
v___x_1595_ = l_Lean_mkConst(v___x_1453_, v___x_1448_);
v___x_1596_ = lean_box(1);
lean_inc(v___x_1594_);
v___x_1597_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1594_, v_levelParams_1454_, v_a_1556_, v___x_1595_, v___x_1596_, v___y_1581_);
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1600_ = v___x_1597_;
v_isShared_1601_ = v_isSharedCheck_1644_;
goto v_resetjp_1599_;
}
else
{
lean_inc(v_a_1598_);
lean_dec(v___x_1597_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1644_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1603_; 
if (v_isShared_1601_ == 0)
{
lean_ctor_set_tag(v___x_1600_, 1);
v___x_1603_ = v___x_1600_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_a_1598_);
v___x_1603_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Lean_addDecl(v___x_1603_, v___x_1444_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; lean_object* v_env_1606_; uint8_t v___x_1607_; 
lean_dec_ref_known(v___x_1604_, 1);
v___x_1605_ = lean_st_ref_get(v___y_1581_);
v_env_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc_ref(v_env_1606_);
lean_dec(v___x_1605_);
v___x_1607_ = l_Lean_isMarkedMeta(v_env_1606_, v_indName_1455_);
if (v___x_1607_ == 0)
{
v___y_1462_ = v___x_1594_;
v___y_1463_ = v___y_1578_;
v___y_1464_ = v___y_1579_;
v___y_1465_ = v___y_1580_;
v___y_1466_ = v___y_1581_;
goto v___jp_1461_;
}
else
{
lean_object* v___x_1608_; lean_object* v_env_1609_; lean_object* v_nextMacroScope_1610_; lean_object* v_ngen_1611_; lean_object* v_auxDeclNGen_1612_; lean_object* v_traceState_1613_; lean_object* v_messages_1614_; lean_object* v_infoState_1615_; lean_object* v_snapshotTasks_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1641_; 
v___x_1608_ = lean_st_ref_take(v___y_1581_);
v_env_1609_ = lean_ctor_get(v___x_1608_, 0);
v_nextMacroScope_1610_ = lean_ctor_get(v___x_1608_, 1);
v_ngen_1611_ = lean_ctor_get(v___x_1608_, 2);
v_auxDeclNGen_1612_ = lean_ctor_get(v___x_1608_, 3);
v_traceState_1613_ = lean_ctor_get(v___x_1608_, 4);
v_messages_1614_ = lean_ctor_get(v___x_1608_, 6);
v_infoState_1615_ = lean_ctor_get(v___x_1608_, 7);
v_snapshotTasks_1616_ = lean_ctor_get(v___x_1608_, 8);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v___x_1608_, 5);
lean_dec(v_unused_1642_);
v___x_1618_ = v___x_1608_;
v_isShared_1619_ = v_isSharedCheck_1641_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_snapshotTasks_1616_);
lean_inc(v_infoState_1615_);
lean_inc(v_messages_1614_);
lean_inc(v_traceState_1613_);
lean_inc(v_auxDeclNGen_1612_);
lean_inc(v_ngen_1611_);
lean_inc(v_nextMacroScope_1610_);
lean_inc(v_env_1609_);
lean_dec(v___x_1608_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1641_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1623_; 
lean_inc(v___x_1594_);
v___x_1620_ = l_Lean_markMeta(v_env_1609_, v___x_1594_);
v___x_1621_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 5, v___x_1621_);
lean_ctor_set(v___x_1618_, 0, v___x_1620_);
v___x_1623_ = v___x_1618_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1640_, 1, v_nextMacroScope_1610_);
lean_ctor_set(v_reuseFailAlloc_1640_, 2, v_ngen_1611_);
lean_ctor_set(v_reuseFailAlloc_1640_, 3, v_auxDeclNGen_1612_);
lean_ctor_set(v_reuseFailAlloc_1640_, 4, v_traceState_1613_);
lean_ctor_set(v_reuseFailAlloc_1640_, 5, v___x_1621_);
lean_ctor_set(v_reuseFailAlloc_1640_, 6, v_messages_1614_);
lean_ctor_set(v_reuseFailAlloc_1640_, 7, v_infoState_1615_);
lean_ctor_set(v_reuseFailAlloc_1640_, 8, v_snapshotTasks_1616_);
v___x_1623_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v_mctx_1626_; lean_object* v_zetaDeltaFVarIds_1627_; lean_object* v_postponed_1628_; lean_object* v_diag_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1638_; 
v___x_1624_ = lean_st_ref_set(v___y_1581_, v___x_1623_);
v___x_1625_ = lean_st_ref_take(v___y_1579_);
v_mctx_1626_ = lean_ctor_get(v___x_1625_, 0);
v_zetaDeltaFVarIds_1627_ = lean_ctor_get(v___x_1625_, 2);
v_postponed_1628_ = lean_ctor_get(v___x_1625_, 3);
v_diag_1629_ = lean_ctor_get(v___x_1625_, 4);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1638_ == 0)
{
lean_object* v_unused_1639_; 
v_unused_1639_ = lean_ctor_get(v___x_1625_, 1);
lean_dec(v_unused_1639_);
v___x_1631_ = v___x_1625_;
v_isShared_1632_ = v_isSharedCheck_1638_;
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
v_isShared_1632_ = v_isSharedCheck_1638_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1633_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 1, v___x_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_mctx_1626_);
lean_ctor_set(v_reuseFailAlloc_1637_, 1, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_zetaDeltaFVarIds_1627_);
lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_postponed_1628_);
lean_ctor_set(v_reuseFailAlloc_1637_, 4, v_diag_1629_);
v___x_1635_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_st_ref_set(v___y_1579_, v___x_1635_);
v___y_1462_ = v___x_1594_;
v___y_1463_ = v___y_1578_;
v___y_1464_ = v___y_1579_;
v___y_1465_ = v___y_1580_;
v___y_1466_ = v___y_1581_;
goto v___jp_1461_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1594_);
lean_dec(v_indName_1455_);
lean_dec(v___x_1453_);
return v___x_1604_;
}
}
}
}
}
}
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
lean_dec(v_a_1556_);
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1448_);
v_a_1646_ = lean_ctor_get(v___x_1584_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1584_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1584_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1584_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_dec(v_a_1556_);
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1448_);
return v___x_1583_;
}
}
else
{
lean_dec(v_a_1556_);
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1448_);
return v___x_1582_;
}
}
v___jp_1654_:
{
lean_object* v___x_1659_; lean_object* v_env_1660_; uint8_t v___x_1661_; 
v___x_1659_ = lean_st_ref_get(v___y_1658_);
v_env_1660_ = lean_ctor_get(v___x_1659_, 0);
lean_inc_ref(v_env_1660_);
lean_dec(v___x_1659_);
lean_inc(v_indName_1455_);
v___x_1661_ = l_Lean_isMarkedMeta(v_env_1660_, v_indName_1455_);
if (v___x_1661_ == 0)
{
v___y_1578_ = v___y_1655_;
v___y_1579_ = v___y_1656_;
v___y_1580_ = v___y_1657_;
v___y_1581_ = v___y_1658_;
goto v___jp_1577_;
}
else
{
lean_object* v___x_1662_; lean_object* v_env_1663_; lean_object* v_nextMacroScope_1664_; lean_object* v_ngen_1665_; lean_object* v_auxDeclNGen_1666_; lean_object* v_traceState_1667_; lean_object* v_messages_1668_; lean_object* v_infoState_1669_; lean_object* v_snapshotTasks_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1695_; 
v___x_1662_ = lean_st_ref_take(v___y_1658_);
v_env_1663_ = lean_ctor_get(v___x_1662_, 0);
v_nextMacroScope_1664_ = lean_ctor_get(v___x_1662_, 1);
v_ngen_1665_ = lean_ctor_get(v___x_1662_, 2);
v_auxDeclNGen_1666_ = lean_ctor_get(v___x_1662_, 3);
v_traceState_1667_ = lean_ctor_get(v___x_1662_, 4);
v_messages_1668_ = lean_ctor_get(v___x_1662_, 6);
v_infoState_1669_ = lean_ctor_get(v___x_1662_, 7);
v_snapshotTasks_1670_ = lean_ctor_get(v___x_1662_, 8);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1695_ == 0)
{
lean_object* v_unused_1696_; 
v_unused_1696_ = lean_ctor_get(v___x_1662_, 5);
lean_dec(v_unused_1696_);
v___x_1672_ = v___x_1662_;
v_isShared_1673_ = v_isSharedCheck_1695_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_snapshotTasks_1670_);
lean_inc(v_infoState_1669_);
lean_inc(v_messages_1668_);
lean_inc(v_traceState_1667_);
lean_inc(v_auxDeclNGen_1666_);
lean_inc(v_ngen_1665_);
lean_inc(v_nextMacroScope_1664_);
lean_inc(v_env_1663_);
lean_dec(v___x_1662_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1695_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
lean_inc(v___x_1453_);
v___x_1674_ = l_Lean_markMeta(v_env_1663_, v___x_1453_);
v___x_1675_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1673_ == 0)
{
lean_ctor_set(v___x_1672_, 5, v___x_1675_);
lean_ctor_set(v___x_1672_, 0, v___x_1674_);
v___x_1677_ = v___x_1672_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v_nextMacroScope_1664_);
lean_ctor_set(v_reuseFailAlloc_1694_, 2, v_ngen_1665_);
lean_ctor_set(v_reuseFailAlloc_1694_, 3, v_auxDeclNGen_1666_);
lean_ctor_set(v_reuseFailAlloc_1694_, 4, v_traceState_1667_);
lean_ctor_set(v_reuseFailAlloc_1694_, 5, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1694_, 6, v_messages_1668_);
lean_ctor_set(v_reuseFailAlloc_1694_, 7, v_infoState_1669_);
lean_ctor_set(v_reuseFailAlloc_1694_, 8, v_snapshotTasks_1670_);
v___x_1677_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_mctx_1680_; lean_object* v_zetaDeltaFVarIds_1681_; lean_object* v_postponed_1682_; lean_object* v_diag_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1692_; 
v___x_1678_ = lean_st_ref_set(v___y_1658_, v___x_1677_);
v___x_1679_ = lean_st_ref_take(v___y_1656_);
v_mctx_1680_ = lean_ctor_get(v___x_1679_, 0);
v_zetaDeltaFVarIds_1681_ = lean_ctor_get(v___x_1679_, 2);
v_postponed_1682_ = lean_ctor_get(v___x_1679_, 3);
v_diag_1683_ = lean_ctor_get(v___x_1679_, 4);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1679_);
if (v_isSharedCheck_1692_ == 0)
{
lean_object* v_unused_1693_; 
v_unused_1693_ = lean_ctor_get(v___x_1679_, 1);
lean_dec(v_unused_1693_);
v___x_1685_ = v___x_1679_;
v_isShared_1686_ = v_isSharedCheck_1692_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_diag_1683_);
lean_inc(v_postponed_1682_);
lean_inc(v_zetaDeltaFVarIds_1681_);
lean_inc(v_mctx_1680_);
lean_dec(v___x_1679_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1692_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v___x_1689_; 
v___x_1687_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v___x_1687_);
v___x_1689_ = v___x_1685_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_mctx_1680_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1687_);
lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_zetaDeltaFVarIds_1681_);
lean_ctor_set(v_reuseFailAlloc_1691_, 3, v_postponed_1682_);
lean_ctor_set(v_reuseFailAlloc_1691_, 4, v_diag_1683_);
v___x_1689_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_st_ref_set(v___y_1656_, v___x_1689_);
v___y_1578_ = v___y_1655_;
v___y_1579_ = v___y_1656_;
v___y_1580_ = v___y_1657_;
v___y_1581_ = v___y_1658_;
goto v___jp_1577_;
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
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1556_);
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1448_);
lean_dec_ref(v_val_1446_);
v_a_1773_ = lean_ctor_get(v___x_1562_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1562_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1562_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1562_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1452_);
lean_dec(v_ctors_1451_);
lean_dec_ref(v___x_1450_);
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
lean_dec_ref(v___x_1447_);
lean_dec_ref(v_val_1446_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec_ref(v___x_1441_);
v_a_1781_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1555_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1555_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v_indName_1455_);
lean_dec(v_levelParams_1454_);
lean_dec(v___x_1453_);
lean_dec(v___x_1452_);
lean_dec(v_ctors_1451_);
lean_dec_ref(v___x_1450_);
lean_dec(v___x_1449_);
lean_dec(v___x_1448_);
lean_dec_ref(v___x_1447_);
lean_dec_ref(v_val_1446_);
lean_dec_ref(v_xs_1443_);
lean_dec_ref(v___x_1442_);
lean_dec_ref(v___x_1441_);
v_a_1789_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1552_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1552_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
v___jp_1461_:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_mk_empty_array_with_capacity(v___x_1467_);
lean_inc(v___y_1462_);
v___x_1469_ = lean_array_push(v___x_1468_, v___y_1462_);
v___x_1470_ = l_Lean_compileDecls(v___x_1469_, v___x_1445_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v___x_1471_; lean_object* v_env_1472_; lean_object* v_nextMacroScope_1473_; lean_object* v_ngen_1474_; lean_object* v_auxDeclNGen_1475_; lean_object* v_traceState_1476_; lean_object* v_messages_1477_; lean_object* v_infoState_1478_; lean_object* v_snapshotTasks_1479_; lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1550_; 
lean_dec_ref_known(v___x_1470_, 1);
v___x_1471_ = lean_st_ref_take(v___y_1466_);
v_env_1472_ = lean_ctor_get(v___x_1471_, 0);
v_nextMacroScope_1473_ = lean_ctor_get(v___x_1471_, 1);
v_ngen_1474_ = lean_ctor_get(v___x_1471_, 2);
v_auxDeclNGen_1475_ = lean_ctor_get(v___x_1471_, 3);
v_traceState_1476_ = lean_ctor_get(v___x_1471_, 4);
v_messages_1477_ = lean_ctor_get(v___x_1471_, 6);
v_infoState_1478_ = lean_ctor_get(v___x_1471_, 7);
v_snapshotTasks_1479_ = lean_ctor_get(v___x_1471_, 8);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v___x_1471_, 5);
lean_dec(v_unused_1551_);
v___x_1481_ = v___x_1471_;
v_isShared_1482_ = v_isSharedCheck_1550_;
goto v_resetjp_1480_;
}
else
{
lean_inc(v_snapshotTasks_1479_);
lean_inc(v_infoState_1478_);
lean_inc(v_messages_1477_);
lean_inc(v_traceState_1476_);
lean_inc(v_auxDeclNGen_1475_);
lean_inc(v_ngen_1474_);
lean_inc(v_nextMacroScope_1473_);
lean_inc(v_env_1472_);
lean_dec(v___x_1471_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1550_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; 
lean_inc(v___y_1462_);
v___x_1483_ = l_Lean_Meta_addToCompletionBlackList(v_env_1472_, v___y_1462_);
v___x_1484_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 5, v___x_1484_);
lean_ctor_set(v___x_1481_, 0, v___x_1483_);
v___x_1486_ = v___x_1481_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_nextMacroScope_1473_);
lean_ctor_set(v_reuseFailAlloc_1549_, 2, v_ngen_1474_);
lean_ctor_set(v_reuseFailAlloc_1549_, 3, v_auxDeclNGen_1475_);
lean_ctor_set(v_reuseFailAlloc_1549_, 4, v_traceState_1476_);
lean_ctor_set(v_reuseFailAlloc_1549_, 5, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1549_, 6, v_messages_1477_);
lean_ctor_set(v_reuseFailAlloc_1549_, 7, v_infoState_1478_);
lean_ctor_set(v_reuseFailAlloc_1549_, 8, v_snapshotTasks_1479_);
v___x_1486_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v_mctx_1489_; lean_object* v_zetaDeltaFVarIds_1490_; lean_object* v_postponed_1491_; lean_object* v_diag_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1547_; 
v___x_1487_ = lean_st_ref_set(v___y_1466_, v___x_1486_);
v___x_1488_ = lean_st_ref_take(v___y_1464_);
v_mctx_1489_ = lean_ctor_get(v___x_1488_, 0);
v_zetaDeltaFVarIds_1490_ = lean_ctor_get(v___x_1488_, 2);
v_postponed_1491_ = lean_ctor_get(v___x_1488_, 3);
v_diag_1492_ = lean_ctor_get(v___x_1488_, 4);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v___x_1488_, 1);
lean_dec(v_unused_1548_);
v___x_1494_ = v___x_1488_;
v_isShared_1495_ = v_isSharedCheck_1547_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_diag_1492_);
lean_inc(v_postponed_1491_);
lean_inc(v_zetaDeltaFVarIds_1490_);
lean_inc(v_mctx_1489_);
lean_dec(v___x_1488_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1547_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
v___x_1496_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1496_);
v___x_1498_ = v___x_1494_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_mctx_1489_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1546_, 2, v_zetaDeltaFVarIds_1490_);
lean_ctor_set(v_reuseFailAlloc_1546_, 3, v_postponed_1491_);
lean_ctor_set(v_reuseFailAlloc_1546_, 4, v_diag_1492_);
v___x_1498_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v_env_1501_; lean_object* v_nextMacroScope_1502_; lean_object* v_ngen_1503_; lean_object* v_auxDeclNGen_1504_; lean_object* v_traceState_1505_; lean_object* v_messages_1506_; lean_object* v_infoState_1507_; lean_object* v_snapshotTasks_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1544_; 
v___x_1499_ = lean_st_ref_set(v___y_1464_, v___x_1498_);
v___x_1500_ = lean_st_ref_take(v___y_1466_);
v_env_1501_ = lean_ctor_get(v___x_1500_, 0);
v_nextMacroScope_1502_ = lean_ctor_get(v___x_1500_, 1);
v_ngen_1503_ = lean_ctor_get(v___x_1500_, 2);
v_auxDeclNGen_1504_ = lean_ctor_get(v___x_1500_, 3);
v_traceState_1505_ = lean_ctor_get(v___x_1500_, 4);
v_messages_1506_ = lean_ctor_get(v___x_1500_, 6);
v_infoState_1507_ = lean_ctor_get(v___x_1500_, 7);
v_snapshotTasks_1508_ = lean_ctor_get(v___x_1500_, 8);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1544_ == 0)
{
lean_object* v_unused_1545_; 
v_unused_1545_ = lean_ctor_get(v___x_1500_, 5);
lean_dec(v_unused_1545_);
v___x_1510_ = v___x_1500_;
v_isShared_1511_ = v_isSharedCheck_1544_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_snapshotTasks_1508_);
lean_inc(v_infoState_1507_);
lean_inc(v_messages_1506_);
lean_inc(v_traceState_1505_);
lean_inc(v_auxDeclNGen_1504_);
lean_inc(v_ngen_1503_);
lean_inc(v_nextMacroScope_1502_);
lean_inc(v_env_1501_);
lean_dec(v___x_1500_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1544_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
lean_inc(v___y_1462_);
v___x_1512_ = l_Lean_addProtected(v_env_1501_, v___y_1462_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 5, v___x_1484_);
lean_ctor_set(v___x_1510_, 0, v___x_1512_);
v___x_1514_ = v___x_1510_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_nextMacroScope_1502_);
lean_ctor_set(v_reuseFailAlloc_1543_, 2, v_ngen_1503_);
lean_ctor_set(v_reuseFailAlloc_1543_, 3, v_auxDeclNGen_1504_);
lean_ctor_set(v_reuseFailAlloc_1543_, 4, v_traceState_1505_);
lean_ctor_set(v_reuseFailAlloc_1543_, 5, v___x_1484_);
lean_ctor_set(v_reuseFailAlloc_1543_, 6, v_messages_1506_);
lean_ctor_set(v_reuseFailAlloc_1543_, 7, v_infoState_1507_);
lean_ctor_set(v_reuseFailAlloc_1543_, 8, v_snapshotTasks_1508_);
v___x_1514_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_mctx_1517_; lean_object* v_zetaDeltaFVarIds_1518_; lean_object* v_postponed_1519_; lean_object* v_diag_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1541_; 
v___x_1515_ = lean_st_ref_set(v___y_1466_, v___x_1514_);
v___x_1516_ = lean_st_ref_take(v___y_1464_);
v_mctx_1517_ = lean_ctor_get(v___x_1516_, 0);
v_zetaDeltaFVarIds_1518_ = lean_ctor_get(v___x_1516_, 2);
v_postponed_1519_ = lean_ctor_get(v___x_1516_, 3);
v_diag_1520_ = lean_ctor_get(v___x_1516_, 4);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1516_, 1);
lean_dec(v_unused_1542_);
v___x_1522_ = v___x_1516_;
v_isShared_1523_ = v_isSharedCheck_1541_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_diag_1520_);
lean_inc(v_postponed_1519_);
lean_inc(v_zetaDeltaFVarIds_1518_);
lean_inc(v_mctx_1517_);
lean_dec(v___x_1516_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1541_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v___x_1496_);
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_mctx_1517_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1540_, 2, v_zetaDeltaFVarIds_1518_);
lean_ctor_set(v_reuseFailAlloc_1540_, 3, v_postponed_1519_);
lean_ctor_set(v_reuseFailAlloc_1540_, 4, v_diag_1520_);
v___x_1525_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1538_; 
v___x_1526_ = lean_st_ref_set(v___y_1464_, v___x_1525_);
lean_inc(v___y_1462_);
v___x_1527_ = l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; 
v_unused_1539_ = lean_ctor_get(v___x_1527_, 0);
lean_dec(v_unused_1539_);
v___x_1529_ = v___x_1527_;
v_isShared_1530_ = v_isSharedCheck_1538_;
goto v_resetjp_1528_;
}
else
{
lean_dec(v___x_1527_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1538_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
lean_ctor_set_tag(v___x_1529_, 1);
lean_ctor_set(v___x_1529_, 0, v___x_1453_);
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1453_);
v___x_1532_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1533_ = lean_box(0);
v___x_1534_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_1535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1532_);
lean_ctor_set(v___x_1535_, 1, v___x_1533_);
lean_ctor_set(v___x_1535_, 2, v___x_1534_);
v___x_1536_ = l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(v___y_1462_, v___x_1535_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1536_;
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
lean_dec(v___y_1462_);
lean_dec(v___x_1453_);
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1797_ = _args[0];
lean_object* v___x_1798_ = _args[1];
lean_object* v_xs_1799_ = _args[2];
lean_object* v___x_1800_ = _args[3];
lean_object* v___x_1801_ = _args[4];
lean_object* v_val_1802_ = _args[5];
lean_object* v___x_1803_ = _args[6];
lean_object* v___x_1804_ = _args[7];
lean_object* v___x_1805_ = _args[8];
lean_object* v___x_1806_ = _args[9];
lean_object* v_ctors_1807_ = _args[10];
lean_object* v___x_1808_ = _args[11];
lean_object* v___x_1809_ = _args[12];
lean_object* v_levelParams_1810_ = _args[13];
lean_object* v_indName_1811_ = _args[14];
lean_object* v___y_1812_ = _args[15];
lean_object* v___y_1813_ = _args[16];
lean_object* v___y_1814_ = _args[17];
lean_object* v___y_1815_ = _args[18];
lean_object* v___y_1816_ = _args[19];
_start:
{
uint8_t v___x_36104__boxed_1817_; uint8_t v___x_36105__boxed_1818_; lean_object* v_res_1819_; 
v___x_36104__boxed_1817_ = lean_unbox(v___x_1800_);
v___x_36105__boxed_1818_ = lean_unbox(v___x_1801_);
v_res_1819_ = l_Lean_mkCtorIdx___lam__1(v___x_1797_, v___x_1798_, v_xs_1799_, v___x_36104__boxed_1817_, v___x_36105__boxed_1818_, v_val_1802_, v___x_1803_, v___x_1804_, v___x_1805_, v___x_1806_, v_ctors_1807_, v___x_1808_, v___x_1809_, v_levelParams_1810_, v_indName_1811_, v___y_1812_, v___y_1813_, v___y_1814_, v___y_1815_);
lean_dec(v___y_1815_);
lean_dec_ref(v___y_1814_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(lean_object* v_bs_1820_, lean_object* v_k_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1820_, v_k_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1835_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1835_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1830_ = v___x_1827_;
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_a_1828_);
lean_dec(v___x_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1835_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
lean_object* v___x_1833_; 
if (v_isShared_1831_ == 0)
{
v___x_1833_ = v___x_1830_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
}
else
{
lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1843_; 
v_a_1836_ = lean_ctor_get(v___x_1827_, 0);
v_isSharedCheck_1843_ = !lean_is_exclusive(v___x_1827_);
if (v_isSharedCheck_1843_ == 0)
{
v___x_1838_ = v___x_1827_;
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1827_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1843_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1841_; 
if (v_isShared_1839_ == 0)
{
v___x_1841_ = v___x_1838_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1842_; 
v_reuseFailAlloc_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_a_1836_);
v___x_1841_ = v_reuseFailAlloc_1842_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
return v___x_1841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object* v_bs_1844_, lean_object* v_k_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(v_bs_1844_, v_k_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_bs_1844_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(size_t v_sz_1852_, size_t v_i_1853_, lean_object* v_bs_1854_){
_start:
{
uint8_t v___x_1855_; 
v___x_1855_ = lean_usize_dec_lt(v_i_1853_, v_sz_1852_);
if (v___x_1855_ == 0)
{
return v_bs_1854_;
}
else
{
lean_object* v_v_1856_; lean_object* v___x_1857_; lean_object* v_bs_x27_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v_v_1856_ = lean_array_uget(v_bs_1854_, v_i_1853_);
v___x_1857_ = lean_unsigned_to_nat(0u);
v_bs_x27_1858_ = lean_array_uset(v_bs_1854_, v_i_1853_, v___x_1857_);
v___x_1859_ = l_Lean_Expr_fvarId_x21(v_v_1856_);
lean_dec(v_v_1856_);
v___x_1860_ = 1;
v___x_1861_ = lean_box(v___x_1860_);
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1859_);
lean_ctor_set(v___x_1862_, 1, v___x_1861_);
v___x_1863_ = ((size_t)1ULL);
v___x_1864_ = lean_usize_add(v_i_1853_, v___x_1863_);
v___x_1865_ = lean_array_uset(v_bs_x27_1858_, v_i_1853_, v___x_1862_);
v_i_1853_ = v___x_1864_;
v_bs_1854_ = v___x_1865_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19___boxed(lean_object* v_sz_1867_, lean_object* v_i_1868_, lean_object* v_bs_1869_){
_start:
{
size_t v_sz_boxed_1870_; size_t v_i_boxed_1871_; lean_object* v_res_1872_; 
v_sz_boxed_1870_ = lean_unbox_usize(v_sz_1867_);
lean_dec(v_sz_1867_);
v_i_boxed_1871_ = lean_unbox_usize(v_i_1868_);
lean_dec(v_i_1868_);
v_res_1872_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(v_sz_boxed_1870_, v_i_boxed_1871_, v_bs_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object* v_bs_1873_, lean_object* v_k_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_, lean_object* v___y_1878_){
_start:
{
size_t v_sz_1880_; size_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; 
v_sz_1880_ = lean_array_size(v_bs_1873_);
v___x_1881_ = ((size_t)0ULL);
v___x_1882_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(v_sz_1880_, v___x_1881_, v_bs_1873_);
v___x_1883_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(v___x_1882_, v_k_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
lean_dec_ref(v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object* v_bs_1884_, lean_object* v_k_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_){
_start:
{
lean_object* v_res_1891_; 
v_res_1891_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(v_bs_1884_, v_k_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_);
lean_dec(v___y_1889_);
lean_dec_ref(v___y_1888_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1895_, lean_object* v_indName_1896_, lean_object* v___x_1897_, lean_object* v___x_1898_, uint8_t v___x_1899_, uint8_t v___x_1900_, lean_object* v_val_1901_, lean_object* v___x_1902_, lean_object* v_ctors_1903_, lean_object* v___x_1904_, lean_object* v_levelParams_1905_, lean_object* v_xs_1906_, lean_object* v_x_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___f_1925_; lean_object* v___x_1926_; 
v___x_1913_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1895_);
lean_inc_ref_n(v_xs_1906_, 3);
v___x_1914_ = l_Array_toSubarray___redArg(v_xs_1906_, v___x_1913_, v_numParams_1895_);
v___x_1915_ = l_Subarray_copy___redArg(v___x_1914_);
v___x_1916_ = lean_array_get_size(v_xs_1906_);
v___x_1917_ = l_Array_toSubarray___redArg(v_xs_1906_, v_numParams_1895_, v___x_1916_);
v___x_1918_ = l_Subarray_copy___redArg(v___x_1917_);
lean_inc(v___x_1897_);
lean_inc(v_indName_1896_);
v___x_1919_ = l_Lean_mkConst(v_indName_1896_, v___x_1897_);
v___x_1920_ = l_Lean_mkAppN(v___x_1919_, v_xs_1906_);
v___x_1921_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1922_ = l_Lean_mkConst(v___x_1921_, v___x_1898_);
v___x_1923_ = lean_box(v___x_1899_);
v___x_1924_ = lean_box(v___x_1900_);
v___f_1925_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1925_, 0, v___x_1920_);
lean_closure_set(v___f_1925_, 1, v___x_1922_);
lean_closure_set(v___f_1925_, 2, v_xs_1906_);
lean_closure_set(v___f_1925_, 3, v___x_1923_);
lean_closure_set(v___f_1925_, 4, v___x_1924_);
lean_closure_set(v___f_1925_, 5, v_val_1901_);
lean_closure_set(v___f_1925_, 6, v___x_1918_);
lean_closure_set(v___f_1925_, 7, v___x_1897_);
lean_closure_set(v___f_1925_, 8, v___x_1902_);
lean_closure_set(v___f_1925_, 9, v___x_1915_);
lean_closure_set(v___f_1925_, 10, v_ctors_1903_);
lean_closure_set(v___f_1925_, 11, v___x_1913_);
lean_closure_set(v___f_1925_, 12, v___x_1904_);
lean_closure_set(v___f_1925_, 13, v_levelParams_1905_);
lean_closure_set(v___f_1925_, 14, v_indName_1896_);
v___x_1926_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(v_xs_1906_, v___f_1925_, v___y_1908_, v___y_1909_, v___y_1910_, v___y_1911_);
return v___x_1926_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1927_ = _args[0];
lean_object* v_indName_1928_ = _args[1];
lean_object* v___x_1929_ = _args[2];
lean_object* v___x_1930_ = _args[3];
lean_object* v___x_1931_ = _args[4];
lean_object* v___x_1932_ = _args[5];
lean_object* v_val_1933_ = _args[6];
lean_object* v___x_1934_ = _args[7];
lean_object* v_ctors_1935_ = _args[8];
lean_object* v___x_1936_ = _args[9];
lean_object* v_levelParams_1937_ = _args[10];
lean_object* v_xs_1938_ = _args[11];
lean_object* v_x_1939_ = _args[12];
lean_object* v___y_1940_ = _args[13];
lean_object* v___y_1941_ = _args[14];
lean_object* v___y_1942_ = _args[15];
lean_object* v___y_1943_ = _args[16];
lean_object* v___y_1944_ = _args[17];
_start:
{
uint8_t v___x_36792__boxed_1945_; uint8_t v___x_36793__boxed_1946_; lean_object* v_res_1947_; 
v___x_36792__boxed_1945_ = lean_unbox(v___x_1931_);
v___x_36793__boxed_1946_ = lean_unbox(v___x_1932_);
v_res_1947_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1927_, v_indName_1928_, v___x_1929_, v___x_1930_, v___x_36792__boxed_1945_, v___x_36793__boxed_1946_, v_val_1933_, v___x_1934_, v_ctors_1935_, v___x_1936_, v_levelParams_1937_, v_xs_1938_, v_x_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
lean_dec_ref(v___y_1940_);
lean_dec_ref(v_x_1939_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
if (lean_obj_tag(v_a_1948_) == 0)
{
lean_object* v___x_1950_; 
v___x_1950_ = l_List_reverse___redArg(v_a_1949_);
return v___x_1950_;
}
else
{
lean_object* v_head_1951_; lean_object* v_tail_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1961_; 
v_head_1951_ = lean_ctor_get(v_a_1948_, 0);
v_tail_1952_ = lean_ctor_get(v_a_1948_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_a_1948_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1954_ = v_a_1948_;
v_isShared_1955_ = v_isSharedCheck_1961_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_tail_1952_);
lean_inc(v_head_1951_);
lean_dec(v_a_1948_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1961_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1956_ = l_Lean_mkLevelParam(v_head_1951_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v_a_1949_);
lean_ctor_set(v___x_1954_, 0, v___x_1956_);
v___x_1958_ = v___x_1954_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1956_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_a_1949_);
v___x_1958_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
v_a_1948_ = v_tail_1952_;
v_a_1949_ = v___x_1958_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1964_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1965_ = lean_unsigned_to_nat(62u);
v___x_1966_ = lean_unsigned_to_nat(50u);
v___x_1967_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1968_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1969_ = l_mkPanicMessageWithDecl(v___x_1968_, v___x_1967_, v___x_1966_, v___x_1965_, v___x_1964_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1970_, uint8_t v___x_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_){
_start:
{
lean_object* v_options_1977_; lean_object* v___x_1978_; uint8_t v___x_1979_; 
v_options_1977_ = lean_ctor_get(v___y_1974_, 2);
v___x_1978_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1979_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_options_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec(v_indName_1970_);
v___x_1980_ = lean_box(0);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
else
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2068_; 
lean_inc(v_indName_1970_);
v___x_1982_ = l_Lean_mkCtorIdxName(v_indName_1970_);
lean_inc(v___x_1982_);
v___x_1983_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1982_, v___x_1979_, v___y_1975_);
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_2068_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2068_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
uint8_t v___x_1988_; 
v___x_1988_ = lean_unbox(v_a_1984_);
lean_dec(v_a_1984_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_del_object(v___x_1986_);
lean_inc(v_indName_1970_);
v___x_1989_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1970_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
if (lean_obj_tag(v_a_1990_) == 5)
{
lean_object* v_val_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2053_; 
v_val_1991_ = lean_ctor_get(v_a_1990_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_1990_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_1993_ = v_a_1990_;
v_isShared_1994_ = v_isSharedCheck_2053_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_val_1991_);
lean_dec(v_a_1990_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2053_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_toConstantVal_1995_; lean_object* v_numParams_1996_; lean_object* v_numIndices_1997_; lean_object* v_ctors_1998_; lean_object* v_levelParams_1999_; lean_object* v_type_2000_; lean_object* v___x_2001_; 
v_toConstantVal_1995_ = lean_ctor_get(v_val_1991_, 0);
v_numParams_1996_ = lean_ctor_get(v_val_1991_, 1);
lean_inc(v_numParams_1996_);
v_numIndices_1997_ = lean_ctor_get(v_val_1991_, 2);
lean_inc(v_numIndices_1997_);
v_ctors_1998_ = lean_ctor_get(v_val_1991_, 4);
lean_inc(v_ctors_1998_);
v_levelParams_1999_ = lean_ctor_get(v_toConstantVal_1995_, 1);
lean_inc(v_levelParams_1999_);
v_type_2000_ = lean_ctor_get(v_toConstantVal_1995_, 2);
lean_inc_ref_n(v_type_2000_, 2);
v___x_2001_ = l_Lean_Meta_isPropFormerType(v_type_2000_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2044_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2044_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2044_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2044_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_unbox(v_a_2002_);
lean_dec(v_a_2002_);
if (v___x_2006_ == 0)
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_del_object(v___x_2004_);
lean_inc(v_indName_1970_);
v___x_2007_ = l_Lean_mkCasesOnName(v_indName_1970_);
lean_inc(v___x_2007_);
v___x_2008_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_2007_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2031_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2011_ = v___x_2008_;
v_isShared_2012_ = v_isSharedCheck_2031_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___x_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2031_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2013_ = l_List_lengthTR___redArg(v_levelParams_1999_);
v___x_2014_ = l_Lean_ConstantInfo_levelParams(v_a_2009_);
lean_dec(v_a_2009_);
v___x_2015_ = l_List_lengthTR___redArg(v___x_2014_);
lean_dec(v___x_2014_);
v___x_2016_ = lean_nat_dec_lt(v___x_2013_, v___x_2015_);
lean_dec(v___x_2015_);
lean_dec(v___x_2013_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2019_; 
lean_dec(v___x_2007_);
lean_dec_ref(v_type_2000_);
lean_dec(v_levelParams_1999_);
lean_dec(v_ctors_1998_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_val_1991_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v___x_2017_ = lean_box(0);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2017_);
v___x_2019_ = v___x_2011_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2017_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___f_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_del_object(v___x_2011_);
v___x_2021_ = lean_box(0);
lean_inc(v_levelParams_1999_);
v___x_2022_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_1999_, v___x_2021_);
v___x_2023_ = lean_box(v___x_1971_);
v___x_2024_ = lean_box(v___x_1979_);
lean_inc(v_numParams_1996_);
v___f_2025_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_2025_, 0, v_numParams_1996_);
lean_closure_set(v___f_2025_, 1, v_indName_1970_);
lean_closure_set(v___f_2025_, 2, v___x_2022_);
lean_closure_set(v___f_2025_, 3, v___x_2021_);
lean_closure_set(v___f_2025_, 4, v___x_2023_);
lean_closure_set(v___f_2025_, 5, v___x_2024_);
lean_closure_set(v___f_2025_, 6, v_val_1991_);
lean_closure_set(v___f_2025_, 7, v___x_2007_);
lean_closure_set(v___f_2025_, 8, v_ctors_1998_);
lean_closure_set(v___f_2025_, 9, v___x_1982_);
lean_closure_set(v___f_2025_, 10, v_levelParams_1999_);
v___x_2026_ = lean_nat_add(v_numParams_1996_, v_numIndices_1997_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set_tag(v___x_1993_, 1);
lean_ctor_set(v___x_1993_, 0, v___x_2026_);
v___x_2028_ = v___x_1993_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; 
v___x_2029_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_2000_, v___x_2028_, v___f_2025_, v___x_1971_, v___x_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_2029_;
}
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v___x_2007_);
lean_dec_ref(v_type_2000_);
lean_dec(v_levelParams_1999_);
lean_dec(v_ctors_1998_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_val_1991_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v_a_2032_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2008_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2008_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_dec_ref(v_type_2000_);
lean_dec(v_levelParams_1999_);
lean_dec(v_ctors_1998_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_val_1991_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v___x_2040_ = lean_box(0);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2040_);
v___x_2042_ = v___x_2004_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec_ref(v_type_2000_);
lean_dec(v_levelParams_1999_);
lean_dec(v_ctors_1998_);
lean_dec(v_numIndices_1997_);
lean_dec(v_numParams_1996_);
lean_del_object(v___x_1993_);
lean_dec_ref(v_val_1991_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v_a_2045_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2001_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2001_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_a_1990_);
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v___x_2054_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_2055_ = l_panic___at___00Lean_mkCtorIdx_spec__13(v___x_2054_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_);
return v___x_2055_;
}
}
else
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2063_; 
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v_a_2056_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_2058_ = v___x_1989_;
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_1989_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2063_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
if (v_isShared_2059_ == 0)
{
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v___x_1982_);
lean_dec(v_indName_1970_);
v___x_2064_ = lean_box(0);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_2064_);
v___x_2066_ = v___x_1986_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2064_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2069_, lean_object* v___x_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
uint8_t v___x_36905__boxed_2076_; lean_object* v_res_2077_; 
v___x_36905__boxed_2076_ = lean_unbox(v___x_2070_);
v_res_2077_ = l_Lean_mkCtorIdx___lam__3(v_indName_2069_, v___x_36905__boxed_2076_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_2078_, lean_object* v_e_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = l_Lean_indentD(v_e_2079_);
v___x_2081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2078_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_2082_, lean_object* v___f_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2082_, v___f_2083_, v___y_2084_, v___y_2085_, v___y_2086_, v___y_2087_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2105_; 
v_a_2098_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2105_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2100_ = v___x_2089_;
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2089_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2105_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2103_; 
if (v_isShared_2101_ == 0)
{
v___x_2103_ = v___x_2100_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
v___x_2103_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
return v___x_2103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_2106_, lean_object* v___f_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Lean_mkCtorIdx___lam__5(v___f_2106_, v___f_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
lean_dec(v___y_2111_);
lean_dec_ref(v___y_2110_);
lean_dec(v___y_2109_);
lean_dec_ref(v___y_2108_);
return v_res_2113_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2126_; uint8_t v___x_2127_; lean_object* v___x_2128_; lean_object* v___f_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___f_2134_; lean_object* v___f_2135_; uint8_t v___x_2136_; uint8_t v___x_2137_; lean_object* v___x_2138_; 
v___x_2126_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_2127_ = 0;
v___x_2128_ = lean_box(v___x_2127_);
lean_inc_n(v_indName_2120_, 2);
v___f_2129_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2129_, 0, v_indName_2120_);
lean_closure_set(v___f_2129_, 1, v___x_2128_);
v___x_2130_ = l_Lean_MessageData_ofConstName(v_indName_2120_, v___x_2127_);
v___x_2131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2126_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_2133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2134_, 0, v___x_2133_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2135_, 0, v___f_2129_);
lean_closure_set(v___f_2135_, 1, v___f_2134_);
v___x_2136_ = l_Lean_isPrivateName(v_indName_2120_);
lean_dec(v_indName_2120_);
v___x_2137_ = lean_bool_not(v___x_2136_);
v___x_2138_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v___f_2135_, v___x_2137_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object* v_indName_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lean_mkCtorIdx(v_indName_2139_, v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
return v_res_2145_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t v___x_2146_, lean_object* v___x_2147_, lean_object* v_as_2148_, lean_object* v_as_x27_2149_, lean_object* v_b_2150_, lean_object* v_a_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_2146_, v___x_2147_, v_as_x27_2149_, v_b_2150_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object* v___x_2158_, lean_object* v___x_2159_, lean_object* v_as_2160_, lean_object* v_as_x27_2161_, lean_object* v_b_2162_, lean_object* v_a_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v___x_37210__boxed_2169_; lean_object* v_res_2170_; 
v___x_37210__boxed_2169_ = lean_unbox(v___x_2158_);
v_res_2170_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_37210__boxed_2169_, v___x_2159_, v_as_2160_, v_as_x27_2161_, v_b_2162_, v_a_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
lean_dec(v___y_2167_);
lean_dec_ref(v___y_2166_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v_as_x27_2161_);
lean_dec(v_as_2160_);
lean_dec_ref(v___x_2159_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2171_, lean_object* v_name_2172_, uint8_t v_bi_2173_, lean_object* v_type_2174_, lean_object* v_k_2175_, uint8_t v_kind_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_2172_, v_bi_2173_, v_type_2174_, v_k_2175_, v_kind_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2183_, lean_object* v_name_2184_, lean_object* v_bi_2185_, lean_object* v_type_2186_, lean_object* v_k_2187_, lean_object* v_kind_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
uint8_t v_bi_boxed_2194_; uint8_t v_kind_boxed_2195_; lean_object* v_res_2196_; 
v_bi_boxed_2194_ = lean_unbox(v_bi_2185_);
v_kind_boxed_2195_ = lean_unbox(v_kind_2188_);
v_res_2196_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(v_00_u03b1_2183_, v_name_2184_, v_bi_boxed_2194_, v_type_2186_, v_k_2187_, v_kind_boxed_2195_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_);
lean_dec(v___y_2192_);
lean_dec_ref(v___y_2191_);
lean_dec(v___y_2190_);
lean_dec_ref(v___y_2189_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object* v_00_u03b1_2197_, lean_object* v_name_2198_, lean_object* v_type_2199_, lean_object* v_k_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; 
v___x_2206_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_2198_, v_type_2199_, v_k_2200_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2207_, lean_object* v_name_2208_, lean_object* v_type_2209_, lean_object* v_k_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(v_00_u03b1_2207_, v_name_2208_, v_type_2209_, v_k_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15(lean_object* v_declName_2217_, uint8_t v_s_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(v_declName_2217_, v_s_2218_, v___y_2220_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_declName_2225_, lean_object* v_s_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
uint8_t v_s_boxed_2232_; lean_object* v_res_2233_; 
v_s_boxed_2232_ = lean_unbox(v_s_2226_);
v_res_2233_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15(v_declName_2225_, v_s_boxed_2232_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17(lean_object* v_env_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(v_env_2234_, v___y_2236_, v___y_2238_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___boxed(lean_object* v_env_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17(v_env_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20(lean_object* v_00_u03b1_2248_, lean_object* v_bs_2249_, lean_object* v_k_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; 
v___x_2256_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(v_bs_2249_, v_k_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___boxed(lean_object* v_00_u03b1_2257_, lean_object* v_bs_2258_, lean_object* v_k_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_res_2265_; 
v_res_2265_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20(v_00_u03b1_2257_, v_bs_2258_, v_k_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_);
lean_dec(v___y_2263_);
lean_dec_ref(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec_ref(v_bs_2258_);
return v_res_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12(lean_object* v_00_u03b1_2266_, lean_object* v_bs_2267_, lean_object* v_k_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v___x_2274_; 
v___x_2274_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(v_bs_2267_, v_k_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_2275_, lean_object* v_bs_2276_, lean_object* v_k_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12(v_00_u03b1_2275_, v_bs_2276_, v_k_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2284_, lean_object* v_constName_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2292_, lean_object* v_constName_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_res_2299_; 
v_res_2299_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(v_00_u03b1_2292_, v_constName_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
return v_res_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2300_, lean_object* v_msg_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2308_, lean_object* v_msg_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(v_00_u03b1_2308_, v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2316_, lean_object* v_ref_2317_, lean_object* v_constName_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2317_, v_constName_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2325_, lean_object* v_ref_2326_, lean_object* v_constName_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2325_, v_ref_2326_, v_constName_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v_ref_2326_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object* v_00_u03b1_2334_, lean_object* v_ref_2335_, lean_object* v_msg_2336_, lean_object* v_declHint_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_2335_, v_msg_2336_, v_declHint_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object* v_00_u03b1_2344_, lean_object* v_ref_2345_, lean_object* v_msg_2346_, lean_object* v_declHint_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_2344_, v_ref_2345_, v_msg_2346_, v_declHint_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v_ref_2345_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object* v_msg_2354_, lean_object* v_declHint_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_2354_, v_declHint_2355_, v___y_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object* v_msg_2362_, lean_object* v_declHint_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_2362_, v_declHint_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object* v_00_u03b1_2370_, lean_object* v_ref_2371_, lean_object* v_msg_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v___x_2378_; 
v___x_2378_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_2371_, v_msg_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2379_, lean_object* v_ref_2380_, lean_object* v_msg_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_2379_, v_ref_2380_, v_msg_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec_ref(v___y_2382_);
lean_dec(v_ref_2380_);
return v_res_2387_;
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
res = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CtorIdx_2118508740____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx);
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
