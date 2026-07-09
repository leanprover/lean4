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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___f_311_; lean_object* v___x_26648__overap_312_; lean_object* v___x_313_; 
v___f_311_ = ((lean_object*)(l_panic___at___00Lean_mkCtorIdx_spec__13___closed__0));
v___x_26648__overap_312_ = lean_panic_fn_borrowed(v___f_311_, v_msg_305_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
v___x_313_ = lean_apply_5(v___x_26648__overap_312_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, lean_box(0));
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
lean_object* v___x_386_; lean_object* v_env_387_; uint8_t v_isExporting_388_; lean_object* v___x_389_; lean_object* v_env_390_; lean_object* v_nextMacroScope_391_; lean_object* v_ngen_392_; lean_object* v_auxDeclNGen_393_; lean_object* v_traceState_394_; lean_object* v_messages_395_; lean_object* v_infoState_396_; lean_object* v_snapshotTasks_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_451_; 
v___x_386_ = lean_st_ref_get(v___y_384_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
v_isExporting_388_ = lean_ctor_get_uint8(v_env_387_, sizeof(void*)*8);
lean_dec_ref(v_env_387_);
v___x_389_ = lean_st_ref_take(v___y_384_);
v_env_390_ = lean_ctor_get(v___x_389_, 0);
v_nextMacroScope_391_ = lean_ctor_get(v___x_389_, 1);
v_ngen_392_ = lean_ctor_get(v___x_389_, 2);
v_auxDeclNGen_393_ = lean_ctor_get(v___x_389_, 3);
v_traceState_394_ = lean_ctor_get(v___x_389_, 4);
v_messages_395_ = lean_ctor_get(v___x_389_, 6);
v_infoState_396_ = lean_ctor_get(v___x_389_, 7);
v_snapshotTasks_397_ = lean_ctor_get(v___x_389_, 8);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; 
v_unused_452_ = lean_ctor_get(v___x_389_, 5);
lean_dec(v_unused_452_);
v___x_399_ = v___x_389_;
v_isShared_400_ = v_isSharedCheck_451_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_snapshotTasks_397_);
lean_inc(v_infoState_396_);
lean_inc(v_messages_395_);
lean_inc(v_traceState_394_);
lean_inc(v_auxDeclNGen_393_);
lean_inc(v_ngen_392_);
lean_inc(v_nextMacroScope_391_);
lean_inc(v_env_390_);
lean_dec(v___x_389_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_451_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = l_Lean_Environment_setExporting(v_env_390_, v_isExporting_380_);
v___x_402_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 5, v___x_402_);
lean_ctor_set(v___x_399_, 0, v___x_401_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_nextMacroScope_391_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_ngen_392_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_auxDeclNGen_393_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_traceState_394_);
lean_ctor_set(v_reuseFailAlloc_450_, 5, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_450_, 6, v_messages_395_);
lean_ctor_set(v_reuseFailAlloc_450_, 7, v_infoState_396_);
lean_ctor_set(v_reuseFailAlloc_450_, 8, v_snapshotTasks_397_);
v___x_404_ = v_reuseFailAlloc_450_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_mctx_407_; lean_object* v_zetaDeltaFVarIds_408_; lean_object* v_postponed_409_; lean_object* v_diag_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_448_; 
v___x_405_ = lean_st_ref_set(v___y_384_, v___x_404_);
v___x_406_ = lean_st_ref_take(v___y_382_);
v_mctx_407_ = lean_ctor_get(v___x_406_, 0);
v_zetaDeltaFVarIds_408_ = lean_ctor_get(v___x_406_, 2);
v_postponed_409_ = lean_ctor_get(v___x_406_, 3);
v_diag_410_ = lean_ctor_get(v___x_406_, 4);
v_isSharedCheck_448_ = !lean_is_exclusive(v___x_406_);
if (v_isSharedCheck_448_ == 0)
{
lean_object* v_unused_449_; 
v_unused_449_ = lean_ctor_get(v___x_406_, 1);
lean_dec(v_unused_449_);
v___x_412_ = v___x_406_;
v_isShared_413_ = v_isSharedCheck_448_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_diag_410_);
lean_inc(v_postponed_409_);
lean_inc(v_zetaDeltaFVarIds_408_);
lean_inc(v_mctx_407_);
lean_dec(v___x_406_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_448_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_414_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 1, v___x_414_);
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_mctx_407_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_zetaDeltaFVarIds_408_);
lean_ctor_set(v_reuseFailAlloc_447_, 3, v_postponed_409_);
lean_ctor_set(v_reuseFailAlloc_447_, 4, v_diag_410_);
v___x_416_ = v_reuseFailAlloc_447_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v_r_418_; 
v___x_417_ = lean_st_ref_set(v___y_382_, v___x_416_);
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
v_r_418_ = lean_apply_5(v_x_379_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, lean_box(0));
if (lean_obj_tag(v_r_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_435_; 
v_a_419_ = lean_ctor_get(v_r_418_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_r_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_421_ = v_r_418_;
v_isShared_422_ = v_isSharedCheck_435_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v_r_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_435_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_424_; 
lean_inc(v_a_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set_tag(v___x_421_, 1);
v___x_424_ = v___x_421_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_a_419_);
v___x_424_ = v_reuseFailAlloc_434_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_432_; 
v___x_425_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0(v___y_384_, v_isExporting_388_, v___x_402_, v___y_382_, v___x_414_, v___x_424_);
lean_dec_ref(v___x_424_);
v_isSharedCheck_432_ = !lean_is_exclusive(v___x_425_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; 
v_unused_433_ = lean_ctor_get(v___x_425_, 0);
lean_dec(v_unused_433_);
v___x_427_ = v___x_425_;
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
else
{
lean_dec(v___x_425_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_432_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v___x_430_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v_a_419_);
v___x_430_ = v___x_427_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_a_419_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
else
{
lean_object* v_a_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_445_; 
v_a_436_ = lean_ctor_get(v_r_418_, 0);
lean_inc(v_a_436_);
lean_dec_ref_known(v_r_418_, 1);
v___x_437_ = lean_box(0);
v___x_438_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___lam__0(v___y_384_, v_isExporting_388_, v___x_402_, v___y_382_, v___x_414_, v___x_437_);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_438_);
if (v_isSharedCheck_445_ == 0)
{
lean_object* v_unused_446_; 
v_unused_446_ = lean_ctor_get(v___x_438_, 0);
lean_dec(v_unused_446_);
v___x_440_ = v___x_438_;
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
else
{
lean_dec(v___x_438_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_445_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set_tag(v___x_440_, 1);
lean_ctor_set(v___x_440_, 0, v_a_436_);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_a_436_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___boxed(lean_object* v_x_453_, lean_object* v_isExporting_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_){
_start:
{
uint8_t v_isExporting_boxed_460_; lean_object* v_res_461_; 
v_isExporting_boxed_460_ = lean_unbox(v_isExporting_454_);
v_res_461_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v_x_453_, v_isExporting_boxed_460_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14(lean_object* v_00_u03b1_462_, lean_object* v_x_463_, uint8_t v_isExporting_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v_x_463_, v_isExporting_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___boxed(lean_object* v_00_u03b1_471_, lean_object* v_x_472_, lean_object* v_isExporting_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
uint8_t v_isExporting_boxed_479_; lean_object* v_res_480_; 
v_isExporting_boxed_479_ = lean_unbox(v_isExporting_473_);
v_res_480_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14(v_00_u03b1_471_, v_x_472_, v_isExporting_boxed_479_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_481_, uint8_t v___x_482_, uint8_t v___x_483_, uint8_t v___x_484_, lean_object* v_ys_485_, lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = l_Lean_mkRawNatLit(v_cidx_481_);
v___x_493_ = l_Lean_Meta_mkLambdaFVars(v_ys_485_, v___x_492_, v___x_482_, v___x_483_, v___x_482_, v___x_483_, v___x_484_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_494_, lean_object* v___x_495_, lean_object* v___x_496_, lean_object* v___x_497_, lean_object* v_ys_498_, lean_object* v_x_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_){
_start:
{
uint8_t v___x_34493__boxed_505_; uint8_t v___x_34494__boxed_506_; uint8_t v___x_34495__boxed_507_; lean_object* v_res_508_; 
v___x_34493__boxed_505_ = lean_unbox(v___x_495_);
v___x_34494__boxed_506_ = lean_unbox(v___x_496_);
v___x_34495__boxed_507_ = lean_unbox(v___x_497_);
v_res_508_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_494_, v___x_34493__boxed_505_, v___x_34494__boxed_506_, v___x_34495__boxed_507_, v_ys_498_, v_x_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_x_499_);
lean_dec_ref(v_ys_498_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v___x_515_; lean_object* v_env_516_; lean_object* v___x_517_; lean_object* v_mctx_518_; lean_object* v_lctx_519_; lean_object* v_options_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_515_ = lean_st_ref_get(v___y_513_);
v_env_516_ = lean_ctor_get(v___x_515_, 0);
lean_inc_ref(v_env_516_);
lean_dec(v___x_515_);
v___x_517_ = lean_st_ref_get(v___y_511_);
v_mctx_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc_ref(v_mctx_518_);
lean_dec(v___x_517_);
v_lctx_519_ = lean_ctor_get(v___y_510_, 2);
v_options_520_ = lean_ctor_get(v___y_512_, 2);
lean_inc_ref(v_options_520_);
lean_inc_ref(v_lctx_519_);
v___x_521_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_521_, 0, v_env_516_);
lean_ctor_set(v___x_521_, 1, v_mctx_518_);
lean_ctor_set(v___x_521_, 2, v_lctx_519_);
lean_ctor_set(v___x_521_, 3, v_options_520_);
v___x_522_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_msgData_509_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_ref_537_; lean_object* v___x_538_; lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_547_; 
v_ref_537_ = lean_ctor_get(v___y_534_, 5);
v___x_538_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msg_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
v_a_539_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_547_ == 0)
{
v___x_541_ = v___x_538_;
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_538_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_547_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_545_; 
lean_inc(v_ref_537_);
v___x_543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_543_, 0, v_ref_537_);
lean_ctor_set(v___x_543_, 1, v_a_539_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 1);
lean_ctor_set(v___x_541_, 0, v___x_543_);
v___x_545_ = v___x_541_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_instMonadEIO(lean_box(0));
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v_toApplicative_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_629_; 
v___x_566_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_567_ = l_StateRefT_x27_instMonad___redArg(v___x_566_);
v_toApplicative_568_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_567_, 1);
lean_dec(v_unused_630_);
v___x_570_ = v___x_567_;
v_isShared_571_ = v_isSharedCheck_629_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_toApplicative_568_);
lean_dec(v___x_567_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_629_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v_toFunctor_572_; lean_object* v_toSeq_573_; lean_object* v_toSeqLeft_574_; lean_object* v_toSeqRight_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_627_; 
v_toFunctor_572_ = lean_ctor_get(v_toApplicative_568_, 0);
v_toSeq_573_ = lean_ctor_get(v_toApplicative_568_, 2);
v_toSeqLeft_574_ = lean_ctor_get(v_toApplicative_568_, 3);
v_toSeqRight_575_ = lean_ctor_get(v_toApplicative_568_, 4);
v_isSharedCheck_627_ = !lean_is_exclusive(v_toApplicative_568_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_toApplicative_568_, 1);
lean_dec(v_unused_628_);
v___x_577_ = v_toApplicative_568_;
v_isShared_578_ = v_isSharedCheck_627_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_toSeqRight_575_);
lean_inc(v_toSeqLeft_574_);
lean_inc(v_toSeq_573_);
lean_inc(v_toFunctor_572_);
lean_dec(v_toApplicative_568_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_627_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___f_579_; lean_object* v___f_580_; lean_object* v___f_581_; lean_object* v___f_582_; lean_object* v___x_583_; lean_object* v___f_584_; lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___x_588_; 
v___f_579_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_580_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_572_);
v___f_581_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_581_, 0, v_toFunctor_572_);
v___f_582_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_582_, 0, v_toFunctor_572_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___f_581_);
lean_ctor_set(v___x_583_, 1, v___f_582_);
v___f_584_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_584_, 0, v_toSeqRight_575_);
v___f_585_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_585_, 0, v_toSeqLeft_574_);
v___f_586_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_586_, 0, v_toSeq_573_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 4, v___f_584_);
lean_ctor_set(v___x_577_, 3, v___f_585_);
lean_ctor_set(v___x_577_, 2, v___f_586_);
lean_ctor_set(v___x_577_, 1, v___f_579_);
lean_ctor_set(v___x_577_, 0, v___x_583_);
v___x_588_ = v___x_577_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___f_579_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v___f_586_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v___f_585_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v___f_584_);
v___x_588_ = v_reuseFailAlloc_626_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_590_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___f_580_);
lean_ctor_set(v___x_570_, 0, v___x_588_);
v___x_590_ = v___x_570_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_588_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___f_580_);
v___x_590_ = v_reuseFailAlloc_625_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v_toApplicative_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_623_; 
v___x_591_ = l_StateRefT_x27_instMonad___redArg(v___x_590_);
v_toApplicative_592_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_623_ == 0)
{
lean_object* v_unused_624_; 
v_unused_624_ = lean_ctor_get(v___x_591_, 1);
lean_dec(v_unused_624_);
v___x_594_ = v___x_591_;
v_isShared_595_ = v_isSharedCheck_623_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_toApplicative_592_);
lean_dec(v___x_591_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_623_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_toFunctor_596_; lean_object* v_toSeq_597_; lean_object* v_toSeqLeft_598_; lean_object* v_toSeqRight_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_621_; 
v_toFunctor_596_ = lean_ctor_get(v_toApplicative_592_, 0);
v_toSeq_597_ = lean_ctor_get(v_toApplicative_592_, 2);
v_toSeqLeft_598_ = lean_ctor_get(v_toApplicative_592_, 3);
v_toSeqRight_599_ = lean_ctor_get(v_toApplicative_592_, 4);
v_isSharedCheck_621_ = !lean_is_exclusive(v_toApplicative_592_);
if (v_isSharedCheck_621_ == 0)
{
lean_object* v_unused_622_; 
v_unused_622_ = lean_ctor_get(v_toApplicative_592_, 1);
lean_dec(v_unused_622_);
v___x_601_ = v_toApplicative_592_;
v_isShared_602_ = v_isSharedCheck_621_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_toSeqRight_599_);
lean_inc(v_toSeqLeft_598_);
lean_inc(v_toSeq_597_);
lean_inc(v_toFunctor_596_);
lean_dec(v_toApplicative_592_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_621_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___f_603_; lean_object* v___f_604_; lean_object* v___f_605_; lean_object* v___f_606_; lean_object* v___x_607_; lean_object* v___f_608_; lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___x_612_; 
v___f_603_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_604_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_596_);
v___f_605_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_605_, 0, v_toFunctor_596_);
v___f_606_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_606_, 0, v_toFunctor_596_);
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___f_605_);
lean_ctor_set(v___x_607_, 1, v___f_606_);
v___f_608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_608_, 0, v_toSeqRight_599_);
v___f_609_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_609_, 0, v_toSeqLeft_598_);
v___f_610_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_610_, 0, v_toSeq_597_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 4, v___f_608_);
lean_ctor_set(v___x_601_, 3, v___f_609_);
lean_ctor_set(v___x_601_, 2, v___f_610_);
lean_ctor_set(v___x_601_, 1, v___f_603_);
lean_ctor_set(v___x_601_, 0, v___x_607_);
v___x_612_ = v___x_601_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___f_603_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v___f_610_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v___f_609_);
lean_ctor_set(v_reuseFailAlloc_620_, 4, v___f_608_);
v___x_612_ = v_reuseFailAlloc_620_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
lean_object* v___x_614_; 
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 1, v___f_604_);
lean_ctor_set(v___x_594_, 0, v___x_612_);
v___x_614_ = v___x_594_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v___f_604_);
v___x_614_ = v_reuseFailAlloc_619_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_30010__overap_617_; lean_object* v___x_618_; 
v___x_615_ = lean_box(0);
v___x_616_ = l_instInhabitedOfMonad___redArg(v___x_614_, v___x_615_);
v___x_30010__overap_617_ = lean_panic_fn_borrowed(v___x_616_, v_msg_560_);
lean_dec(v___x_616_);
lean_inc(v___y_564_);
lean_inc_ref(v___y_563_);
lean_inc(v___y_562_);
lean_inc_ref(v___y_561_);
v___x_618_ = lean_apply_5(v___x_30010__overap_617_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, lean_box(0));
return v___x_618_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_637_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_648_ = lean_unsigned_to_nat(11u);
v___x_649_ = lean_unsigned_to_nat(122u);
v___x_650_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_651_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_652_ = l_mkPanicMessageWithDecl(v___x_651_, v___x_650_, v___x_649_, v___x_648_, v___x_647_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_667_; lean_object* v_env_668_; uint8_t v___x_669_; lean_object* v___x_670_; 
v___x_667_ = lean_st_ref_get(v___y_657_);
v_env_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc_ref(v_env_668_);
lean_dec(v___x_667_);
v___x_669_ = 0;
lean_inc(v_constName_653_);
v___x_670_ = l_Lean_Environment_findAsync_x3f(v_env_668_, v_constName_653_, v___x_669_);
if (lean_obj_tag(v___x_670_) == 1)
{
lean_object* v_val_671_; uint8_t v_kind_672_; 
v_val_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v___x_670_, 1);
v_kind_672_ = lean_ctor_get_uint8(v_val_671_, sizeof(void*)*3);
if (v_kind_672_ == 6)
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_671_);
if (lean_obj_tag(v___x_673_) == 6)
{
lean_object* v_val_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec(v_constName_653_);
v_val_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_val_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
lean_ctor_set_tag(v___x_676_, 0);
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_val_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref(v___x_673_);
v___x_682_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_683_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_682_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_a_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
if (lean_obj_tag(v_a_684_) == 0)
{
lean_del_object(v___x_686_);
goto v___jp_659_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_690_; 
lean_dec(v_constName_653_);
v_val_688_ = lean_ctor_get(v_a_684_, 0);
lean_inc(v_val_688_);
lean_dec_ref_known(v_a_684_, 1);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v_val_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v_val_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
lean_dec(v_constName_653_);
v_a_693_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_683_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_683_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
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
}
else
{
lean_dec(v_val_671_);
goto v___jp_659_;
}
}
else
{
lean_dec(v___x_670_);
goto v___jp_659_;
}
v___jp_659_:
{
lean_object* v___x_660_; uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_660_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_661_ = 0;
v___x_662_ = l_Lean_MessageData_ofConstName(v_constName_653_, v___x_661_);
v___x_663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_660_);
lean_ctor_set(v___x_663_, 1, v___x_662_);
v___x_664_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_665_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_);
lean_dec(v___y_705_);
lean_dec_ref(v___y_704_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_708_, lean_object* v___x_709_, lean_object* v_as_x27_710_, lean_object* v_b_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
if (lean_obj_tag(v_as_x27_710_) == 0)
{
lean_object* v___x_717_; 
v___x_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_717_, 0, v_b_711_);
return v___x_717_;
}
else
{
lean_object* v_head_718_; lean_object* v_tail_719_; lean_object* v___x_720_; 
v_head_718_ = lean_ctor_get(v_as_x27_710_, 0);
v_tail_719_ = lean_ctor_get(v_as_x27_710_, 1);
lean_inc(v_head_718_);
v___x_720_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_718_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v_toConstantVal_722_; lean_object* v_cidx_723_; lean_object* v_numFields_724_; lean_object* v_type_725_; lean_object* v___x_726_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
lean_inc(v_a_721_);
lean_dec_ref_known(v___x_720_, 1);
v_toConstantVal_722_ = lean_ctor_get(v_a_721_, 0);
lean_inc_ref(v_toConstantVal_722_);
v_cidx_723_ = lean_ctor_get(v_a_721_, 2);
lean_inc(v_cidx_723_);
v_numFields_724_ = lean_ctor_get(v_a_721_, 4);
lean_inc(v_numFields_724_);
lean_dec(v_a_721_);
v_type_725_ = lean_ctor_get(v_toConstantVal_722_, 2);
lean_inc_ref(v_type_725_);
lean_dec_ref(v_toConstantVal_722_);
v___x_726_ = l_Lean_Meta_instantiateForall(v_type_725_, v___x_709_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_744_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_744_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_744_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_744_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___f_736_; lean_object* v___x_738_; 
v___x_731_ = 0;
v___x_732_ = 1;
v___x_733_ = lean_box(v___x_731_);
v___x_734_ = lean_box(v___x_708_);
v___x_735_ = lean_box(v___x_732_);
v___f_736_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_736_, 0, v_cidx_723_);
lean_closure_set(v___f_736_, 1, v___x_733_);
lean_closure_set(v___f_736_, 2, v___x_734_);
lean_closure_set(v___f_736_, 3, v___x_735_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 1);
lean_ctor_set(v___x_729_, 0, v_numFields_724_);
v___x_738_ = v___x_729_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_numFields_724_);
v___x_738_ = v_reuseFailAlloc_743_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_727_, v___x_738_, v___f_736_, v___x_731_, v___x_731_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = l_Lean_Expr_app___override(v_b_711_, v_a_740_);
v_as_x27_710_ = v_tail_719_;
v_b_711_ = v___x_741_;
goto _start;
}
else
{
lean_dec_ref(v_b_711_);
return v___x_739_;
}
}
}
}
else
{
lean_dec(v_numFields_724_);
lean_dec(v_cidx_723_);
lean_dec_ref(v_b_711_);
return v___x_726_;
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v_b_711_);
v_a_745_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_720_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_720_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_753_, lean_object* v___x_754_, lean_object* v_as_x27_755_, lean_object* v_b_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
uint8_t v___x_34865__boxed_762_; lean_object* v_res_763_; 
v___x_34865__boxed_762_ = lean_unbox(v___x_753_);
v_res_763_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_34865__boxed_762_, v___x_754_, v_as_x27_755_, v_b_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
lean_dec(v___y_758_);
lean_dec_ref(v___y_757_);
lean_dec(v_as_x27_755_);
lean_dec_ref(v___x_754_);
return v_res_763_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = lean_box(0);
v___x_765_ = l_Lean_Level_succ___override(v___x_764_);
return v___x_765_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_766_, uint8_t v___x_767_, uint8_t v___x_768_, uint8_t v___x_769_, lean_object* v_val_770_, lean_object* v___x_771_, lean_object* v___x_772_, lean_object* v___x_773_, lean_object* v___x_774_, lean_object* v___x_775_, lean_object* v_ctors_776_, lean_object* v___x_777_, lean_object* v_x_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_value_785_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = l_Lean_InductiveVal_numCtors(v_val_770_);
v___x_789_ = lean_unsigned_to_nat(1u);
v___x_790_ = lean_nat_dec_eq(v___x_788_, v___x_789_);
lean_dec(v___x_788_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec(v___x_777_);
lean_inc_ref(v_x_778_);
lean_inc_ref(v___x_771_);
v___x_791_ = lean_array_push(v___x_771_, v_x_778_);
v___x_792_ = l_Lean_Meta_mkLambdaFVars(v___x_791_, v___x_772_, v___x_767_, v___x_768_, v___x_767_, v___x_768_, v___x_769_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec_ref(v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___x_773_);
v___x_796_ = l_Lean_mkConst(v___x_774_, v___x_795_);
v___x_797_ = l_Lean_mkAppN(v___x_796_, v___x_775_);
v___x_798_ = l_Lean_Expr_app___override(v___x_797_, v_a_793_);
v___x_799_ = l_Lean_mkAppN(v___x_798_, v___x_771_);
lean_dec_ref(v___x_771_);
lean_inc_ref(v_x_778_);
v___x_800_ = l_Lean_Expr_app___override(v___x_799_, v_x_778_);
v___x_801_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_768_, v___x_775_, v_ctors_776_, v___x_800_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
v_value_785_ = v_a_802_;
goto v___jp_784_;
}
else
{
lean_dec_ref(v_x_778_);
lean_dec_ref(v_xs_766_);
return v___x_801_;
}
}
else
{
lean_dec_ref(v_x_778_);
lean_dec(v___x_774_);
lean_dec(v___x_773_);
lean_dec_ref(v___x_771_);
lean_dec_ref(v_xs_766_);
return v___x_792_;
}
}
else
{
lean_object* v___x_803_; 
lean_dec(v___x_774_);
lean_dec(v___x_773_);
lean_dec_ref(v___x_772_);
lean_dec_ref(v___x_771_);
v___x_803_ = l_Lean_mkRawNatLit(v___x_777_);
v_value_785_ = v___x_803_;
goto v___jp_784_;
}
v___jp_784_:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_array_push(v_xs_766_, v_x_778_);
v___x_787_ = l_Lean_Meta_mkLambdaFVars(v___x_786_, v_value_785_, v___x_767_, v___x_768_, v___x_767_, v___x_768_, v___x_769_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec_ref(v___x_786_);
return v___x_787_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_804_ = _args[0];
lean_object* v___x_805_ = _args[1];
lean_object* v___x_806_ = _args[2];
lean_object* v___x_807_ = _args[3];
lean_object* v_val_808_ = _args[4];
lean_object* v___x_809_ = _args[5];
lean_object* v___x_810_ = _args[6];
lean_object* v___x_811_ = _args[7];
lean_object* v___x_812_ = _args[8];
lean_object* v___x_813_ = _args[9];
lean_object* v_ctors_814_ = _args[10];
lean_object* v___x_815_ = _args[11];
lean_object* v_x_816_ = _args[12];
lean_object* v___y_817_ = _args[13];
lean_object* v___y_818_ = _args[14];
lean_object* v___y_819_ = _args[15];
lean_object* v___y_820_ = _args[16];
lean_object* v___y_821_ = _args[17];
_start:
{
uint8_t v___x_34956__boxed_822_; uint8_t v___x_34957__boxed_823_; uint8_t v___x_34958__boxed_824_; lean_object* v_res_825_; 
v___x_34956__boxed_822_ = lean_unbox(v___x_805_);
v___x_34957__boxed_823_ = lean_unbox(v___x_806_);
v___x_34958__boxed_824_ = lean_unbox(v___x_807_);
v_res_825_ = l_Lean_mkCtorIdx___lam__0(v_xs_804_, v___x_34956__boxed_822_, v___x_34957__boxed_823_, v___x_34958__boxed_824_, v_val_808_, v___x_809_, v___x_810_, v___x_811_, v___x_812_, v___x_813_, v_ctors_814_, v___x_815_, v_x_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
lean_dec(v_ctors_814_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v_val_808_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_826_, lean_object* v_b_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_){
_start:
{
lean_object* v___x_833_; 
lean_inc(v___y_831_);
lean_inc_ref(v___y_830_);
lean_inc(v___y_829_);
lean_inc_ref(v___y_828_);
v___x_833_ = lean_apply_6(v_k_826_, v_b_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, lean_box(0));
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_834_, v_b_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_842_, uint8_t v_bi_843_, lean_object* v_type_844_, lean_object* v_k_845_, uint8_t v_kind_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___f_852_; lean_object* v___x_853_; 
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_852_, 0, v_k_845_);
v___x_853_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_842_, v_bi_843_, v_type_844_, v___f_852_, v_kind_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
v_a_862_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_853_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_853_);
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
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_870_, lean_object* v_bi_871_, lean_object* v_type_872_, lean_object* v_k_873_, lean_object* v_kind_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v_bi_boxed_880_; uint8_t v_kind_boxed_881_; lean_object* v_res_882_; 
v_bi_boxed_880_ = lean_unbox(v_bi_871_);
v_kind_boxed_881_ = lean_unbox(v_kind_874_);
v_res_882_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_870_, v_bi_boxed_880_, v_type_872_, v_k_873_, v_kind_boxed_881_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_883_, lean_object* v_type_884_, lean_object* v_k_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
uint8_t v___x_891_; uint8_t v___x_892_; lean_object* v___x_893_; 
v___x_891_ = 0;
v___x_892_ = 0;
v___x_893_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_883_, v___x_891_, v_type_884_, v_k_885_, v___x_892_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_894_, lean_object* v_type_895_, lean_object* v_k_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_894_, v_type_895_, v_k_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(lean_object* v_declName_903_, uint8_t v_s_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; lean_object* v_env_909_; lean_object* v_nextMacroScope_910_; lean_object* v_ngen_911_; lean_object* v_auxDeclNGen_912_; lean_object* v_traceState_913_; lean_object* v_messages_914_; lean_object* v_infoState_915_; lean_object* v_snapshotTasks_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_945_; 
v___x_908_ = lean_st_ref_take(v___y_906_);
v_env_909_ = lean_ctor_get(v___x_908_, 0);
v_nextMacroScope_910_ = lean_ctor_get(v___x_908_, 1);
v_ngen_911_ = lean_ctor_get(v___x_908_, 2);
v_auxDeclNGen_912_ = lean_ctor_get(v___x_908_, 3);
v_traceState_913_ = lean_ctor_get(v___x_908_, 4);
v_messages_914_ = lean_ctor_get(v___x_908_, 6);
v_infoState_915_ = lean_ctor_get(v___x_908_, 7);
v_snapshotTasks_916_ = lean_ctor_get(v___x_908_, 8);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_945_ == 0)
{
lean_object* v_unused_946_; 
v_unused_946_ = lean_ctor_get(v___x_908_, 5);
lean_dec(v_unused_946_);
v___x_918_ = v___x_908_;
v_isShared_919_ = v_isSharedCheck_945_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_snapshotTasks_916_);
lean_inc(v_infoState_915_);
lean_inc(v_messages_914_);
lean_inc(v_traceState_913_);
lean_inc(v_auxDeclNGen_912_);
lean_inc(v_ngen_911_);
lean_inc(v_nextMacroScope_910_);
lean_inc(v_env_909_);
lean_dec(v___x_908_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_945_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
uint8_t v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_920_ = 0;
v___x_921_ = lean_box(0);
v___x_922_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_909_, v_declName_903_, v_s_904_, v___x_920_, v___x_921_);
v___x_923_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 5, v___x_923_);
lean_ctor_set(v___x_918_, 0, v___x_922_);
v___x_925_ = v___x_918_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_944_, 1, v_nextMacroScope_910_);
lean_ctor_set(v_reuseFailAlloc_944_, 2, v_ngen_911_);
lean_ctor_set(v_reuseFailAlloc_944_, 3, v_auxDeclNGen_912_);
lean_ctor_set(v_reuseFailAlloc_944_, 4, v_traceState_913_);
lean_ctor_set(v_reuseFailAlloc_944_, 5, v___x_923_);
lean_ctor_set(v_reuseFailAlloc_944_, 6, v_messages_914_);
lean_ctor_set(v_reuseFailAlloc_944_, 7, v_infoState_915_);
lean_ctor_set(v_reuseFailAlloc_944_, 8, v_snapshotTasks_916_);
v___x_925_ = v_reuseFailAlloc_944_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v_mctx_928_; lean_object* v_zetaDeltaFVarIds_929_; lean_object* v_postponed_930_; lean_object* v_diag_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_942_; 
v___x_926_ = lean_st_ref_set(v___y_906_, v___x_925_);
v___x_927_ = lean_st_ref_take(v___y_905_);
v_mctx_928_ = lean_ctor_get(v___x_927_, 0);
v_zetaDeltaFVarIds_929_ = lean_ctor_get(v___x_927_, 2);
v_postponed_930_ = lean_ctor_get(v___x_927_, 3);
v_diag_931_ = lean_ctor_get(v___x_927_, 4);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_942_ == 0)
{
lean_object* v_unused_943_; 
v_unused_943_ = lean_ctor_get(v___x_927_, 1);
lean_dec(v_unused_943_);
v___x_933_ = v___x_927_;
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_diag_931_);
lean_inc(v_postponed_930_);
lean_inc(v_zetaDeltaFVarIds_929_);
lean_inc(v_mctx_928_);
lean_dec(v___x_927_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 1, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_mctx_928_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_941_, 2, v_zetaDeltaFVarIds_929_);
lean_ctor_set(v_reuseFailAlloc_941_, 3, v_postponed_930_);
lean_ctor_set(v_reuseFailAlloc_941_, 4, v_diag_931_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_938_ = lean_st_ref_set(v___y_905_, v___x_937_);
v___x_939_ = lean_box(0);
v___x_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_940_, 0, v___x_939_);
return v___x_940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object* v_declName_947_, lean_object* v_s_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
uint8_t v_s_boxed_952_; lean_object* v_res_953_; 
v_s_boxed_952_ = lean_unbox(v_s_948_);
v_res_953_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(v_declName_947_, v_s_boxed_952_, v___y_949_, v___y_950_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(lean_object* v_declName_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
uint8_t v___x_960_; lean_object* v___x_961_; 
v___x_960_ = 0;
v___x_961_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(v_declName_954_, v___x_960_, v___y_956_, v___y_958_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_declName_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(v_declName_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_968_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_969_; 
v___x_969_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_969_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_970_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
v___x_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_970_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
lean_ctor_set(v___x_974_, 1, v___x_973_);
lean_ctor_set(v___x_974_, 2, v___x_973_);
lean_ctor_set(v___x_974_, 3, v___x_973_);
lean_ctor_set(v___x_974_, 4, v___x_972_);
lean_ctor_set(v___x_974_, 5, v___x_972_);
lean_ctor_set(v___x_974_, 6, v___x_972_);
lean_ctor_set(v___x_974_, 7, v___x_972_);
lean_ctor_set(v___x_974_, 8, v___x_972_);
lean_ctor_set(v___x_974_, 9, v___x_972_);
return v___x_974_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_975_ = lean_unsigned_to_nat(32u);
v___x_976_ = lean_mk_empty_array_with_capacity(v___x_975_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_978_ = ((size_t)5ULL);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_unsigned_to_nat(32u);
v___x_981_ = lean_mk_empty_array_with_capacity(v___x_980_);
v___x_982_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
v___x_983_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_981_);
lean_ctor_set(v___x_983_, 2, v___x_979_);
lean_ctor_set(v___x_983_, 3, v___x_979_);
lean_ctor_set_usize(v___x_983_, 4, v___x_978_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_984_ = lean_box(1);
v___x_985_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
v___x_986_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_985_);
lean_ctor_set(v___x_987_, 2, v___x_984_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_989_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6));
v___x_990_ = l_Lean_stringToMessageData(v___x_989_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8));
v___x_993_ = l_Lean_stringToMessageData(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object* v_msg_1009_, lean_object* v_declHint_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; lean_object* v_env_1014_; uint8_t v___x_1015_; 
v___x_1013_ = lean_st_ref_get(v___y_1011_);
v_env_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc_ref(v_env_1014_);
lean_dec(v___x_1013_);
v___x_1015_ = l_Lean_Name_isAnonymous(v_declHint_1010_);
if (v___x_1015_ == 0)
{
uint8_t v_isExporting_1016_; 
v_isExporting_1016_ = lean_ctor_get_uint8(v_env_1014_, sizeof(void*)*8);
if (v_isExporting_1016_ == 0)
{
lean_object* v___x_1017_; 
lean_dec_ref(v_env_1014_);
lean_dec(v_declHint_1010_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v_msg_1009_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; uint8_t v___x_1019_; 
lean_inc_ref(v_env_1014_);
v___x_1018_ = l_Lean_Environment_setExporting(v_env_1014_, v___x_1015_);
lean_inc(v_declHint_1010_);
lean_inc_ref(v___x_1018_);
v___x_1019_ = l_Lean_Environment_contains(v___x_1018_, v_declHint_1010_, v_isExporting_1016_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_dec_ref(v___x_1018_);
lean_dec_ref(v_env_1014_);
lean_dec(v_declHint_1010_);
v___x_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1020_, 0, v_msg_1009_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v_c_1026_; lean_object* v___x_1027_; 
v___x_1021_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
v___x_1022_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
v___x_1023_ = l_Lean_Options_empty;
v___x_1024_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1018_);
lean_ctor_set(v___x_1024_, 1, v___x_1021_);
lean_ctor_set(v___x_1024_, 2, v___x_1022_);
lean_ctor_set(v___x_1024_, 3, v___x_1023_);
lean_inc(v_declHint_1010_);
v___x_1025_ = l_Lean_MessageData_ofConstName(v_declHint_1010_, v___x_1015_);
v_c_1026_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1026_, 0, v___x_1024_);
lean_ctor_set(v_c_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1014_, v_declHint_1010_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_dec_ref(v_env_1014_);
lean_dec(v_declHint_1010_);
v___x_1028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_1029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v_c_1026_);
v___x_1030_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
v___x_1031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
lean_ctor_set(v___x_1031_, 1, v___x_1030_);
v___x_1032_ = l_Lean_MessageData_note(v___x_1031_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v_msg_1009_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
return v___x_1034_;
}
else
{
lean_object* v_val_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1070_; 
v_val_1035_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1037_ = v___x_1027_;
v_isShared_1038_ = v_isSharedCheck_1070_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_val_1035_);
lean_dec(v___x_1027_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1070_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v_mod_1042_; uint8_t v___x_1043_; 
v___x_1039_ = lean_box(0);
v___x_1040_ = l_Lean_Environment_header(v_env_1014_);
lean_dec_ref(v_env_1014_);
v___x_1041_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1040_);
v_mod_1042_ = lean_array_get(v___x_1039_, v___x_1041_, v_val_1035_);
lean_dec(v_val_1035_);
lean_dec_ref(v___x_1041_);
v___x_1043_ = l_Lean_isPrivateName(v_declHint_1010_);
lean_dec(v_declHint_1010_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1055_; 
v___x_1044_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_c_1026_);
v___x_1046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
v___x_1047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1045_);
lean_ctor_set(v___x_1047_, 1, v___x_1046_);
v___x_1048_ = l_Lean_MessageData_ofName(v_mod_1042_);
v___x_1049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1047_);
lean_ctor_set(v___x_1049_, 1, v___x_1048_);
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1049_);
lean_ctor_set(v___x_1051_, 1, v___x_1050_);
v___x_1052_ = l_Lean_MessageData_note(v___x_1051_);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v_msg_1009_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1053_);
v___x_1055_ = v___x_1037_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_1058_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v_c_1026_);
v___x_1059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
v___x_1060_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1058_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
v___x_1061_ = l_Lean_MessageData_ofName(v_mod_1042_);
v___x_1062_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1060_);
lean_ctor_set(v___x_1062_, 1, v___x_1061_);
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1062_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v___x_1065_ = l_Lean_MessageData_note(v___x_1064_);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_msg_1009_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set_tag(v___x_1037_, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1066_);
v___x_1068_ = v___x_1037_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1071_; 
lean_dec_ref(v_env_1014_);
lean_dec(v_declHint_1010_);
v___x_1071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1071_, 0, v_msg_1009_);
return v___x_1071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_1072_, v_declHint_1073_, v___y_1074_);
lean_dec(v___y_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object* v_msg_1077_, lean_object* v_declHint_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1094_; 
v___x_1084_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_1077_, v_declHint_1078_, v___y_1082_);
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1094_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1089_ = l_Lean_unknownIdentifierMessageTag;
v___x_1090_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1090_, 0, v___x_1089_);
lean_ctor_set(v___x_1090_, 1, v_a_1085_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1090_);
v___x_1092_ = v___x_1087_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object* v_msg_1095_, lean_object* v_declHint_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_1095_, v_declHint_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object* v_ref_1103_, lean_object* v_msg_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_fileName_1110_; lean_object* v_fileMap_1111_; lean_object* v_options_1112_; lean_object* v_currRecDepth_1113_; lean_object* v_maxRecDepth_1114_; lean_object* v_ref_1115_; lean_object* v_currNamespace_1116_; lean_object* v_openDecls_1117_; lean_object* v_initHeartbeats_1118_; lean_object* v_maxHeartbeats_1119_; lean_object* v_quotContext_1120_; lean_object* v_currMacroScope_1121_; uint8_t v_diag_1122_; lean_object* v_cancelTk_x3f_1123_; uint8_t v_suppressElabErrors_1124_; lean_object* v_inheritedTraceOptions_1125_; lean_object* v_ref_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_fileName_1110_ = lean_ctor_get(v___y_1107_, 0);
v_fileMap_1111_ = lean_ctor_get(v___y_1107_, 1);
v_options_1112_ = lean_ctor_get(v___y_1107_, 2);
v_currRecDepth_1113_ = lean_ctor_get(v___y_1107_, 3);
v_maxRecDepth_1114_ = lean_ctor_get(v___y_1107_, 4);
v_ref_1115_ = lean_ctor_get(v___y_1107_, 5);
v_currNamespace_1116_ = lean_ctor_get(v___y_1107_, 6);
v_openDecls_1117_ = lean_ctor_get(v___y_1107_, 7);
v_initHeartbeats_1118_ = lean_ctor_get(v___y_1107_, 8);
v_maxHeartbeats_1119_ = lean_ctor_get(v___y_1107_, 9);
v_quotContext_1120_ = lean_ctor_get(v___y_1107_, 10);
v_currMacroScope_1121_ = lean_ctor_get(v___y_1107_, 11);
v_diag_1122_ = lean_ctor_get_uint8(v___y_1107_, sizeof(void*)*14);
v_cancelTk_x3f_1123_ = lean_ctor_get(v___y_1107_, 12);
v_suppressElabErrors_1124_ = lean_ctor_get_uint8(v___y_1107_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1125_ = lean_ctor_get(v___y_1107_, 13);
v_ref_1126_ = l_Lean_replaceRef(v_ref_1103_, v_ref_1115_);
lean_inc_ref(v_inheritedTraceOptions_1125_);
lean_inc(v_cancelTk_x3f_1123_);
lean_inc(v_currMacroScope_1121_);
lean_inc(v_quotContext_1120_);
lean_inc(v_maxHeartbeats_1119_);
lean_inc(v_initHeartbeats_1118_);
lean_inc(v_openDecls_1117_);
lean_inc(v_currNamespace_1116_);
lean_inc(v_maxRecDepth_1114_);
lean_inc(v_currRecDepth_1113_);
lean_inc_ref(v_options_1112_);
lean_inc_ref(v_fileMap_1111_);
lean_inc_ref(v_fileName_1110_);
v___x_1127_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1127_, 0, v_fileName_1110_);
lean_ctor_set(v___x_1127_, 1, v_fileMap_1111_);
lean_ctor_set(v___x_1127_, 2, v_options_1112_);
lean_ctor_set(v___x_1127_, 3, v_currRecDepth_1113_);
lean_ctor_set(v___x_1127_, 4, v_maxRecDepth_1114_);
lean_ctor_set(v___x_1127_, 5, v_ref_1126_);
lean_ctor_set(v___x_1127_, 6, v_currNamespace_1116_);
lean_ctor_set(v___x_1127_, 7, v_openDecls_1117_);
lean_ctor_set(v___x_1127_, 8, v_initHeartbeats_1118_);
lean_ctor_set(v___x_1127_, 9, v_maxHeartbeats_1119_);
lean_ctor_set(v___x_1127_, 10, v_quotContext_1120_);
lean_ctor_set(v___x_1127_, 11, v_currMacroScope_1121_);
lean_ctor_set(v___x_1127_, 12, v_cancelTk_x3f_1123_);
lean_ctor_set(v___x_1127_, 13, v_inheritedTraceOptions_1125_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*14, v_diag_1122_);
lean_ctor_set_uint8(v___x_1127_, sizeof(void*)*14 + 1, v_suppressElabErrors_1124_);
v___x_1128_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1104_, v___y_1105_, v___y_1106_, v___x_1127_, v___y_1108_);
lean_dec_ref_known(v___x_1127_, 14);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object* v_ref_1129_, lean_object* v_msg_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_1129_, v_msg_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
lean_dec(v___y_1132_);
lean_dec_ref(v___y_1131_);
lean_dec(v_ref_1129_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object* v_ref_1137_, lean_object* v_msg_1138_, lean_object* v_declHint_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1145_; lean_object* v_a_1146_; lean_object* v___x_1147_; 
v___x_1145_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_1138_, v_declHint_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref(v___x_1145_);
v___x_1147_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_1137_, v_a_1146_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1148_, lean_object* v_msg_1149_, lean_object* v_declHint_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1148_, v_msg_1149_, v_declHint_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
lean_dec(v___y_1154_);
lean_dec_ref(v___y_1153_);
lean_dec(v___y_1152_);
lean_dec_ref(v___y_1151_);
lean_dec(v_ref_1148_);
return v_res_1156_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1159_ = l_Lean_stringToMessageData(v___x_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1160_, lean_object* v_constName_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v___x_1167_; uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1167_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1168_ = 0;
lean_inc(v_constName_1161_);
v___x_1169_ = l_Lean_MessageData_ofConstName(v_constName_1161_, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1167_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1160_, v___x_1172_, v_constName_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1174_, lean_object* v_constName_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1174_, v_constName_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
lean_dec(v___y_1177_);
lean_dec_ref(v___y_1176_);
lean_dec(v_ref_1174_);
return v_res_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_ref_1188_; lean_object* v___x_1189_; 
v_ref_1188_ = lean_ctor_get(v___y_1185_, 5);
v___x_1189_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1188_, v_constName_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; lean_object* v_env_1204_; uint8_t v___x_1205_; lean_object* v___x_1206_; 
v___x_1203_ = lean_st_ref_get(v___y_1201_);
v_env_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc_ref(v_env_1204_);
lean_dec(v___x_1203_);
v___x_1205_ = 0;
lean_inc(v_constName_1197_);
v___x_1206_ = l_Lean_Environment_find_x3f(v_env_1204_, v_constName_1197_, v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
return v___x_1207_;
}
else
{
lean_object* v_val_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1215_; 
lean_dec(v_constName_1197_);
v_val_1208_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1210_ = v___x_1206_;
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_val_1208_);
lean_dec(v___x_1206_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1215_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1213_; 
if (v_isShared_1211_ == 0)
{
lean_ctor_set_tag(v___x_1210_, 0);
v___x_1213_ = v___x_1210_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_val_1208_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1216_, v___y_1217_, v___y_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(uint8_t v___x_1223_, lean_object* v_x_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
if (lean_obj_tag(v_x_1224_) == 0)
{
uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1230_ = 1;
v___x_1231_ = lean_box(v___x_1230_);
v___x_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
return v___x_1232_;
}
else
{
lean_object* v_head_1233_; lean_object* v_tail_1234_; lean_object* v___x_1235_; 
v_head_1233_ = lean_ctor_get(v_x_1224_, 0);
lean_inc(v_head_1233_);
v_tail_1234_ = lean_ctor_get(v_x_1224_, 1);
lean_inc(v_tail_1234_);
lean_dec_ref_known(v_x_1224_, 2);
v___x_1235_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_head_1233_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
if (lean_obj_tag(v___x_1235_) == 0)
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1256_; 
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1256_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1256_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___y_1241_; uint8_t v_a_1242_; 
if (lean_obj_tag(v_a_1236_) == 6)
{
lean_object* v_val_1244_; lean_object* v_numFields_1245_; lean_object* v___x_1246_; uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v_val_1244_ = lean_ctor_get(v_a_1236_, 0);
lean_inc_ref(v_val_1244_);
lean_dec_ref_known(v_a_1236_, 1);
v_numFields_1245_ = lean_ctor_get(v_val_1244_, 4);
lean_inc(v_numFields_1245_);
lean_dec_ref(v_val_1244_);
v___x_1246_ = lean_unsigned_to_nat(0u);
v___x_1247_ = lean_nat_dec_eq(v_numFields_1245_, v___x_1246_);
lean_dec(v_numFields_1245_);
v___x_1248_ = lean_box(v___x_1247_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1248_);
v___x_1250_ = v___x_1238_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
v___y_1241_ = v___x_1250_;
v_a_1242_ = v___x_1247_;
goto v___jp_1240_;
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1254_; 
lean_dec(v_a_1236_);
v___x_1252_ = lean_box(v___x_1223_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1252_);
v___x_1254_ = v___x_1238_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1252_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
v___y_1241_ = v___x_1254_;
v_a_1242_ = v___x_1223_;
goto v___jp_1240_;
}
}
v___jp_1240_:
{
if (v_a_1242_ == 0)
{
lean_dec(v_tail_1234_);
return v___y_1241_;
}
else
{
lean_dec_ref(v___y_1241_);
v_x_1224_ = v_tail_1234_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v_tail_1234_);
v_a_1257_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1235_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1235_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
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
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v___x_1265_, lean_object* v_x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_35662__boxed_1272_; lean_object* v_res_1273_; 
v___x_35662__boxed_1272_ = lean_unbox(v___x_1265_);
v_res_1273_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(v___x_35662__boxed_1272_, v_x_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(lean_object* v_declName_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_declName_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1336_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1283_ = v___x_1280_;
v_isShared_1284_ = v_isSharedCheck_1336_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1280_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1336_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
if (lean_obj_tag(v_a_1281_) == 5)
{
lean_object* v_val_1285_; lean_object* v_toConstantVal_1286_; lean_object* v_numParams_1287_; lean_object* v_numIndices_1288_; lean_object* v_ctors_1289_; uint8_t v_isRec_1290_; uint8_t v_isUnsafe_1291_; lean_object* v_type_1292_; uint8_t v___x_1293_; 
v_val_1285_ = lean_ctor_get(v_a_1281_, 0);
lean_inc_ref(v_val_1285_);
lean_dec_ref_known(v_a_1281_, 1);
v_toConstantVal_1286_ = lean_ctor_get(v_val_1285_, 0);
v_numParams_1287_ = lean_ctor_get(v_val_1285_, 1);
lean_inc(v_numParams_1287_);
v_numIndices_1288_ = lean_ctor_get(v_val_1285_, 2);
lean_inc(v_numIndices_1288_);
v_ctors_1289_ = lean_ctor_get(v_val_1285_, 4);
lean_inc(v_ctors_1289_);
v_isRec_1290_ = lean_ctor_get_uint8(v_val_1285_, sizeof(void*)*6);
v_isUnsafe_1291_ = lean_ctor_get_uint8(v_val_1285_, sizeof(void*)*6 + 1);
v_type_1292_ = lean_ctor_get(v_toConstantVal_1286_, 2);
v___x_1293_ = l_Lean_Expr_isProp(v_type_1292_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1294_ = l_Lean_InductiveVal_numTypeFormers(v_val_1285_);
lean_dec_ref(v_val_1285_);
v___x_1295_ = lean_unsigned_to_nat(1u);
v___x_1296_ = lean_nat_dec_eq(v___x_1294_, v___x_1295_);
lean_dec(v___x_1294_);
if (v___x_1296_ == 0)
{
lean_object* v___x_1297_; lean_object* v___x_1299_; 
lean_dec(v_ctors_1289_);
lean_dec(v_numIndices_1288_);
lean_dec(v_numParams_1287_);
v___x_1297_ = lean_box(v___x_1296_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1297_);
v___x_1299_ = v___x_1283_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_nat_dec_eq(v_numIndices_1288_, v___x_1301_);
lean_dec(v_numIndices_1288_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_dec(v_ctors_1289_);
lean_dec(v_numParams_1287_);
v___x_1303_ = lean_box(v___x_1302_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1303_);
v___x_1305_ = v___x_1283_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_nat_dec_eq(v_numParams_1287_, v___x_1301_);
lean_dec(v_numParams_1287_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1310_; 
lean_dec(v_ctors_1289_);
v___x_1308_ = lean_box(v___x_1307_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1308_);
v___x_1310_ = v___x_1283_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1308_);
v___x_1310_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
return v___x_1310_;
}
}
else
{
uint8_t v___x_1312_; 
v___x_1312_ = l_List_isEmpty___redArg(v_ctors_1289_);
if (v___x_1312_ == 0)
{
if (v_isRec_1290_ == 0)
{
if (v_isUnsafe_1291_ == 0)
{
lean_object* v___x_1313_; 
lean_del_object(v___x_1283_);
v___x_1313_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(v_isUnsafe_1291_, v_ctors_1289_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec(v_ctors_1289_);
v___x_1314_ = lean_box(v_isRec_1290_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1314_);
v___x_1316_ = v___x_1283_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
lean_dec(v_ctors_1289_);
v___x_1318_ = lean_box(v___x_1312_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1318_);
v___x_1320_ = v___x_1283_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
lean_dec(v_ctors_1289_);
v___x_1322_ = lean_box(v___x_1293_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1322_);
v___x_1324_ = v___x_1283_;
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
}
}
}
}
else
{
uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
lean_dec(v_ctors_1289_);
lean_dec(v_numIndices_1288_);
lean_dec(v_numParams_1287_);
lean_dec_ref(v_val_1285_);
v___x_1326_ = 0;
v___x_1327_ = lean_box(v___x_1326_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1327_);
v___x_1329_ = v___x_1283_;
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
}
else
{
uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
lean_dec(v_a_1281_);
v___x_1331_ = 0;
v___x_1332_ = lean_box(v___x_1331_);
if (v_isShared_1284_ == 0)
{
lean_ctor_set(v___x_1283_, 0, v___x_1332_);
v___x_1334_ = v___x_1283_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
v_a_1337_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1280_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1280_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_declName_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(v_declName_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(lean_object* v_env_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v_nextMacroScope_1357_; lean_object* v_ngen_1358_; lean_object* v_auxDeclNGen_1359_; lean_object* v_traceState_1360_; lean_object* v_messages_1361_; lean_object* v_infoState_1362_; lean_object* v_snapshotTasks_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1389_; 
v___x_1356_ = lean_st_ref_take(v___y_1354_);
v_nextMacroScope_1357_ = lean_ctor_get(v___x_1356_, 1);
v_ngen_1358_ = lean_ctor_get(v___x_1356_, 2);
v_auxDeclNGen_1359_ = lean_ctor_get(v___x_1356_, 3);
v_traceState_1360_ = lean_ctor_get(v___x_1356_, 4);
v_messages_1361_ = lean_ctor_get(v___x_1356_, 6);
v_infoState_1362_ = lean_ctor_get(v___x_1356_, 7);
v_snapshotTasks_1363_ = lean_ctor_get(v___x_1356_, 8);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1389_ == 0)
{
lean_object* v_unused_1390_; lean_object* v_unused_1391_; 
v_unused_1390_ = lean_ctor_get(v___x_1356_, 5);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v___x_1356_, 0);
lean_dec(v_unused_1391_);
v___x_1365_ = v___x_1356_;
v_isShared_1366_ = v_isSharedCheck_1389_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snapshotTasks_1363_);
lean_inc(v_infoState_1362_);
lean_inc(v_messages_1361_);
lean_inc(v_traceState_1360_);
lean_inc(v_auxDeclNGen_1359_);
lean_inc(v_ngen_1358_);
lean_inc(v_nextMacroScope_1357_);
lean_dec(v___x_1356_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1389_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1369_; 
v___x_1367_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 5, v___x_1367_);
lean_ctor_set(v___x_1365_, 0, v_env_1352_);
v___x_1369_ = v___x_1365_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_env_1352_);
lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_nextMacroScope_1357_);
lean_ctor_set(v_reuseFailAlloc_1388_, 2, v_ngen_1358_);
lean_ctor_set(v_reuseFailAlloc_1388_, 3, v_auxDeclNGen_1359_);
lean_ctor_set(v_reuseFailAlloc_1388_, 4, v_traceState_1360_);
lean_ctor_set(v_reuseFailAlloc_1388_, 5, v___x_1367_);
lean_ctor_set(v_reuseFailAlloc_1388_, 6, v_messages_1361_);
lean_ctor_set(v_reuseFailAlloc_1388_, 7, v_infoState_1362_);
lean_ctor_set(v_reuseFailAlloc_1388_, 8, v_snapshotTasks_1363_);
v___x_1369_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v_mctx_1372_; lean_object* v_zetaDeltaFVarIds_1373_; lean_object* v_postponed_1374_; lean_object* v_diag_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1386_; 
v___x_1370_ = lean_st_ref_set(v___y_1354_, v___x_1369_);
v___x_1371_ = lean_st_ref_take(v___y_1353_);
v_mctx_1372_ = lean_ctor_get(v___x_1371_, 0);
v_zetaDeltaFVarIds_1373_ = lean_ctor_get(v___x_1371_, 2);
v_postponed_1374_ = lean_ctor_get(v___x_1371_, 3);
v_diag_1375_ = lean_ctor_get(v___x_1371_, 4);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v___x_1371_, 1);
lean_dec(v_unused_1387_);
v___x_1377_ = v___x_1371_;
v_isShared_1378_ = v_isSharedCheck_1386_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_diag_1375_);
lean_inc(v_postponed_1374_);
lean_inc(v_zetaDeltaFVarIds_1373_);
lean_inc(v_mctx_1372_);
lean_dec(v___x_1371_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1386_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1378_ == 0)
{
lean_ctor_set(v___x_1377_, 1, v___x_1379_);
v___x_1381_ = v___x_1377_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_mctx_1372_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v___x_1379_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_zetaDeltaFVarIds_1373_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_postponed_1374_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v_diag_1375_);
v___x_1381_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = lean_st_ref_set(v___y_1353_, v___x_1381_);
v___x_1383_ = lean_box(0);
v___x_1384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
return v___x_1384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object* v_env_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(v_env_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec(v___y_1393_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(lean_object* v_declName_1397_, lean_object* v_entry_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1404_ = lean_st_ref_get(v___y_1402_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = l_Lean_Linter_deprecatedAttr;
v___x_1407_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1406_, v_env_1405_, v_declName_1397_, v_entry_1398_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1417_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1417_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set_tag(v___x_1410_, 3);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1414_ = l_Lean_MessageData_ofFormat(v___x_1413_);
v___x_1415_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_1414_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
return v___x_1415_;
}
}
}
else
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1407_, 1);
v___x_1419_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(v_a_1418_, v___y_1400_, v___y_1402_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object* v_declName_1420_, lean_object* v_entry_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(v_declName_1420_, v_entry_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_1434_, lean_object* v___x_1435_, lean_object* v_xs_1436_, uint8_t v___x_1437_, uint8_t v___x_1438_, lean_object* v_val_1439_, lean_object* v___x_1440_, lean_object* v___x_1441_, lean_object* v___x_1442_, lean_object* v___x_1443_, lean_object* v_ctors_1444_, lean_object* v___x_1445_, lean_object* v___x_1446_, lean_object* v_levelParams_1447_, lean_object* v_indName_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___y_1455_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___x_1545_; 
lean_inc_ref(v___x_1435_);
lean_inc_ref(v___x_1434_);
v___x_1545_ = l_Lean_mkArrow(v___x_1434_, v___x_1435_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
v___x_1547_ = 1;
v___x_1548_ = l_Lean_Meta_mkForallFVars(v_xs_1436_, v_a_1546_, v___x_1437_, v___x_1438_, v___x_1438_, v___x_1547_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v___x_1548_, 1);
v___x_1550_ = lean_box(v___x_1437_);
v___x_1551_ = lean_box(v___x_1438_);
v___x_1552_ = lean_box(v___x_1547_);
lean_inc(v___x_1441_);
lean_inc_ref(v_val_1439_);
v___f_1553_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1553_, 0, v_xs_1436_);
lean_closure_set(v___f_1553_, 1, v___x_1550_);
lean_closure_set(v___f_1553_, 2, v___x_1551_);
lean_closure_set(v___f_1553_, 3, v___x_1552_);
lean_closure_set(v___f_1553_, 4, v_val_1439_);
lean_closure_set(v___f_1553_, 5, v___x_1440_);
lean_closure_set(v___f_1553_, 6, v___x_1435_);
lean_closure_set(v___f_1553_, 7, v___x_1441_);
lean_closure_set(v___f_1553_, 8, v___x_1442_);
lean_closure_set(v___f_1553_, 9, v___x_1443_);
lean_closure_set(v___f_1553_, 10, v_ctors_1444_);
lean_closure_set(v___f_1553_, 11, v___x_1445_);
v___x_1554_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__3));
v___x_1555_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_1554_, v___x_1434_, v___f_1553_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v_env_1558_; uint32_t v___x_1559_; uint32_t v___x_1560_; uint32_t v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1765_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc_n(v_a_1556_, 2);
lean_dec_ref_known(v___x_1555_, 1);
v___x_1557_ = lean_st_ref_get(v___y_1452_);
v_env_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc_ref(v_env_1558_);
lean_dec(v___x_1557_);
v___x_1559_ = l_Lean_getMaxHeight(v_env_1558_, v_a_1556_);
v___x_1560_ = 1;
v___x_1561_ = lean_uint32_add(v___x_1559_, v___x_1560_);
v___x_1562_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1562_, 0, v___x_1561_);
lean_inc(v_a_1549_);
lean_inc(v_levelParams_1447_);
lean_inc(v___x_1446_);
v___x_1563_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1446_, v_levelParams_1447_, v_a_1549_, v_a_1556_, v___x_1562_, v___y_1452_);
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1765_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1765_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set_tag(v___x_1566_, 1);
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___x_1690_; 
lean_inc_ref(v___x_1569_);
v___x_1690_ = l_Lean_addDecl(v___x_1569_, v___x_1437_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; lean_object* v_env_1692_; lean_object* v_nextMacroScope_1693_; lean_object* v_ngen_1694_; lean_object* v_auxDeclNGen_1695_; lean_object* v_traceState_1696_; lean_object* v_messages_1697_; lean_object* v_infoState_1698_; lean_object* v_snapshotTasks_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1762_; 
lean_dec_ref_known(v___x_1690_, 1);
v___x_1691_ = lean_st_ref_take(v___y_1452_);
v_env_1692_ = lean_ctor_get(v___x_1691_, 0);
v_nextMacroScope_1693_ = lean_ctor_get(v___x_1691_, 1);
v_ngen_1694_ = lean_ctor_get(v___x_1691_, 2);
v_auxDeclNGen_1695_ = lean_ctor_get(v___x_1691_, 3);
v_traceState_1696_ = lean_ctor_get(v___x_1691_, 4);
v_messages_1697_ = lean_ctor_get(v___x_1691_, 6);
v_infoState_1698_ = lean_ctor_get(v___x_1691_, 7);
v_snapshotTasks_1699_ = lean_ctor_get(v___x_1691_, 8);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; 
v_unused_1763_ = lean_ctor_get(v___x_1691_, 5);
lean_dec(v_unused_1763_);
v___x_1701_ = v___x_1691_;
v_isShared_1702_ = v_isSharedCheck_1762_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_snapshotTasks_1699_);
lean_inc(v_infoState_1698_);
lean_inc(v_messages_1697_);
lean_inc(v_traceState_1696_);
lean_inc(v_auxDeclNGen_1695_);
lean_inc(v_ngen_1694_);
lean_inc(v_nextMacroScope_1693_);
lean_inc(v_env_1692_);
lean_dec(v___x_1691_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1762_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1706_; 
lean_inc(v___x_1446_);
v___x_1703_ = l_Lean_Meta_addToCompletionBlackList(v_env_1692_, v___x_1446_);
v___x_1704_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 5, v___x_1704_);
lean_ctor_set(v___x_1701_, 0, v___x_1703_);
v___x_1706_ = v___x_1701_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1703_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_nextMacroScope_1693_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_ngen_1694_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_auxDeclNGen_1695_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_traceState_1696_);
lean_ctor_set(v_reuseFailAlloc_1761_, 5, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1761_, 6, v_messages_1697_);
lean_ctor_set(v_reuseFailAlloc_1761_, 7, v_infoState_1698_);
lean_ctor_set(v_reuseFailAlloc_1761_, 8, v_snapshotTasks_1699_);
v___x_1706_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v_mctx_1709_; lean_object* v_zetaDeltaFVarIds_1710_; lean_object* v_postponed_1711_; lean_object* v_diag_1712_; lean_object* v___x_1714_; uint8_t v_isShared_1715_; uint8_t v_isSharedCheck_1759_; 
v___x_1707_ = lean_st_ref_set(v___y_1452_, v___x_1706_);
v___x_1708_ = lean_st_ref_take(v___y_1450_);
v_mctx_1709_ = lean_ctor_get(v___x_1708_, 0);
v_zetaDeltaFVarIds_1710_ = lean_ctor_get(v___x_1708_, 2);
v_postponed_1711_ = lean_ctor_get(v___x_1708_, 3);
v_diag_1712_ = lean_ctor_get(v___x_1708_, 4);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v___x_1708_, 1);
lean_dec(v_unused_1760_);
v___x_1714_ = v___x_1708_;
v_isShared_1715_ = v_isSharedCheck_1759_;
goto v_resetjp_1713_;
}
else
{
lean_inc(v_diag_1712_);
lean_inc(v_postponed_1711_);
lean_inc(v_zetaDeltaFVarIds_1710_);
lean_inc(v_mctx_1709_);
lean_dec(v___x_1708_);
v___x_1714_ = lean_box(0);
v_isShared_1715_ = v_isSharedCheck_1759_;
goto v_resetjp_1713_;
}
v_resetjp_1713_:
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1716_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1715_ == 0)
{
lean_ctor_set(v___x_1714_, 1, v___x_1716_);
v___x_1718_ = v___x_1714_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_mctx_1709_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_zetaDeltaFVarIds_1710_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_postponed_1711_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_diag_1712_);
v___x_1718_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v_env_1721_; lean_object* v_nextMacroScope_1722_; lean_object* v_ngen_1723_; lean_object* v_auxDeclNGen_1724_; lean_object* v_traceState_1725_; lean_object* v_messages_1726_; lean_object* v_infoState_1727_; lean_object* v_snapshotTasks_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1756_; 
v___x_1719_ = lean_st_ref_set(v___y_1450_, v___x_1718_);
v___x_1720_ = lean_st_ref_take(v___y_1452_);
v_env_1721_ = lean_ctor_get(v___x_1720_, 0);
v_nextMacroScope_1722_ = lean_ctor_get(v___x_1720_, 1);
v_ngen_1723_ = lean_ctor_get(v___x_1720_, 2);
v_auxDeclNGen_1724_ = lean_ctor_get(v___x_1720_, 3);
v_traceState_1725_ = lean_ctor_get(v___x_1720_, 4);
v_messages_1726_ = lean_ctor_get(v___x_1720_, 6);
v_infoState_1727_ = lean_ctor_get(v___x_1720_, 7);
v_snapshotTasks_1728_ = lean_ctor_get(v___x_1720_, 8);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v___x_1720_, 5);
lean_dec(v_unused_1757_);
v___x_1730_ = v___x_1720_;
v_isShared_1731_ = v_isSharedCheck_1756_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_snapshotTasks_1728_);
lean_inc(v_infoState_1727_);
lean_inc(v_messages_1726_);
lean_inc(v_traceState_1725_);
lean_inc(v_auxDeclNGen_1724_);
lean_inc(v_ngen_1723_);
lean_inc(v_nextMacroScope_1722_);
lean_inc(v_env_1721_);
lean_dec(v___x_1720_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1756_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
lean_inc(v___x_1446_);
v___x_1732_ = l_Lean_addProtected(v_env_1721_, v___x_1446_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 5, v___x_1704_);
lean_ctor_set(v___x_1730_, 0, v___x_1732_);
v___x_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1755_, 1, v_nextMacroScope_1722_);
lean_ctor_set(v_reuseFailAlloc_1755_, 2, v_ngen_1723_);
lean_ctor_set(v_reuseFailAlloc_1755_, 3, v_auxDeclNGen_1724_);
lean_ctor_set(v_reuseFailAlloc_1755_, 4, v_traceState_1725_);
lean_ctor_set(v_reuseFailAlloc_1755_, 5, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1755_, 6, v_messages_1726_);
lean_ctor_set(v_reuseFailAlloc_1755_, 7, v_infoState_1727_);
lean_ctor_set(v_reuseFailAlloc_1755_, 8, v_snapshotTasks_1728_);
v___x_1734_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v_mctx_1737_; lean_object* v_zetaDeltaFVarIds_1738_; lean_object* v_postponed_1739_; lean_object* v_diag_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1753_; 
v___x_1735_ = lean_st_ref_set(v___y_1452_, v___x_1734_);
v___x_1736_ = lean_st_ref_take(v___y_1450_);
v_mctx_1737_ = lean_ctor_get(v___x_1736_, 0);
v_zetaDeltaFVarIds_1738_ = lean_ctor_get(v___x_1736_, 2);
v_postponed_1739_ = lean_ctor_get(v___x_1736_, 3);
v_diag_1740_ = lean_ctor_get(v___x_1736_, 4);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1753_ == 0)
{
lean_object* v_unused_1754_; 
v_unused_1754_ = lean_ctor_get(v___x_1736_, 1);
lean_dec(v_unused_1754_);
v___x_1742_ = v___x_1736_;
v_isShared_1743_ = v_isSharedCheck_1753_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_diag_1740_);
lean_inc(v_postponed_1739_);
lean_inc(v_zetaDeltaFVarIds_1738_);
lean_inc(v_mctx_1737_);
lean_dec(v___x_1736_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1753_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v___x_1716_);
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_mctx_1737_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v___x_1716_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_zetaDeltaFVarIds_1738_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_postponed_1739_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v_diag_1740_);
v___x_1745_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; uint8_t v___x_1749_; 
v___x_1746_ = lean_st_ref_set(v___y_1450_, v___x_1745_);
v___x_1747_ = lean_unsigned_to_nat(1u);
v___x_1748_ = l_Lean_InductiveVal_numCtors(v_val_1439_);
lean_dec_ref(v_val_1439_);
v___x_1749_ = lean_nat_dec_eq(v___x_1748_, v___x_1747_);
lean_dec(v___x_1748_);
if (v___x_1749_ == 0)
{
v___y_1648_ = v___y_1449_;
v___y_1649_ = v___y_1450_;
v___y_1650_ = v___y_1451_;
v___y_1651_ = v___y_1452_;
goto v___jp_1647_;
}
else
{
uint8_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = 2;
lean_inc(v___x_1446_);
v___x_1751_ = l_Lean_Meta_setInlineAttribute(v___x_1446_, v___x_1750_, v___y_1449_, v___y_1450_, v___y_1451_, v___y_1452_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_dec_ref_known(v___x_1751_, 1);
v___y_1648_ = v___y_1449_;
v___y_1649_ = v___y_1450_;
v___y_1650_ = v___y_1451_;
v___y_1651_ = v___y_1452_;
goto v___jp_1647_;
}
else
{
lean_dec_ref(v___x_1569_);
lean_dec(v_a_1549_);
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1441_);
return v___x_1751_;
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
lean_dec_ref(v___x_1569_);
lean_dec(v_a_1549_);
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1441_);
lean_dec_ref(v_val_1439_);
return v___x_1690_;
}
v___jp_1570_:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_compileDecl(v___x_1569_, v___x_1438_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref_known(v___x_1575_, 1);
lean_inc(v___x_1446_);
v___x_1576_ = l_Lean_enableRealizationsForConst(v___x_1446_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; 
lean_dec_ref_known(v___x_1576_, 1);
lean_inc(v_indName_1448_);
v___x_1577_ = l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(v_indName_1448_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1638_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1638_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1638_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
uint8_t v___x_1582_; 
v___x_1582_ = lean_unbox(v_a_1578_);
lean_dec(v_a_1578_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
lean_dec(v_a_1549_);
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1441_);
v___x_1583_ = lean_box(0);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1583_);
v___x_1585_ = v___x_1580_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1637_; 
lean_del_object(v___x_1580_);
lean_inc(v_indName_1448_);
v___x_1587_ = l_Lean_mkToCtorIdxName(v_indName_1448_);
lean_inc(v___x_1446_);
v___x_1588_ = l_Lean_mkConst(v___x_1446_, v___x_1441_);
v___x_1589_ = lean_box(1);
lean_inc(v___x_1587_);
v___x_1590_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1587_, v_levelParams_1447_, v_a_1549_, v___x_1588_, v___x_1589_, v___y_1574_);
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1590_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1593_ = v___x_1590_;
v_isShared_1594_ = v_isSharedCheck_1637_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v___x_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1637_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 1);
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1591_);
v___x_1596_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_addDecl(v___x_1596_, v___x_1437_, v___y_1573_, v___y_1574_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v___x_1598_; lean_object* v_env_1599_; uint8_t v___x_1600_; 
lean_dec_ref_known(v___x_1597_, 1);
v___x_1598_ = lean_st_ref_get(v___y_1574_);
v_env_1599_ = lean_ctor_get(v___x_1598_, 0);
lean_inc_ref(v_env_1599_);
lean_dec(v___x_1598_);
v___x_1600_ = l_Lean_isMarkedMeta(v_env_1599_, v_indName_1448_);
if (v___x_1600_ == 0)
{
v___y_1455_ = v___x_1587_;
v___y_1456_ = v___y_1571_;
v___y_1457_ = v___y_1572_;
v___y_1458_ = v___y_1573_;
v___y_1459_ = v___y_1574_;
goto v___jp_1454_;
}
else
{
lean_object* v___x_1601_; lean_object* v_env_1602_; lean_object* v_nextMacroScope_1603_; lean_object* v_ngen_1604_; lean_object* v_auxDeclNGen_1605_; lean_object* v_traceState_1606_; lean_object* v_messages_1607_; lean_object* v_infoState_1608_; lean_object* v_snapshotTasks_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1634_; 
v___x_1601_ = lean_st_ref_take(v___y_1574_);
v_env_1602_ = lean_ctor_get(v___x_1601_, 0);
v_nextMacroScope_1603_ = lean_ctor_get(v___x_1601_, 1);
v_ngen_1604_ = lean_ctor_get(v___x_1601_, 2);
v_auxDeclNGen_1605_ = lean_ctor_get(v___x_1601_, 3);
v_traceState_1606_ = lean_ctor_get(v___x_1601_, 4);
v_messages_1607_ = lean_ctor_get(v___x_1601_, 6);
v_infoState_1608_ = lean_ctor_get(v___x_1601_, 7);
v_snapshotTasks_1609_ = lean_ctor_get(v___x_1601_, 8);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; 
v_unused_1635_ = lean_ctor_get(v___x_1601_, 5);
lean_dec(v_unused_1635_);
v___x_1611_ = v___x_1601_;
v_isShared_1612_ = v_isSharedCheck_1634_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_snapshotTasks_1609_);
lean_inc(v_infoState_1608_);
lean_inc(v_messages_1607_);
lean_inc(v_traceState_1606_);
lean_inc(v_auxDeclNGen_1605_);
lean_inc(v_ngen_1604_);
lean_inc(v_nextMacroScope_1603_);
lean_inc(v_env_1602_);
lean_dec(v___x_1601_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1634_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
lean_inc(v___x_1587_);
v___x_1613_ = l_Lean_markMeta(v_env_1602_, v___x_1587_);
v___x_1614_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 5, v___x_1614_);
lean_ctor_set(v___x_1611_, 0, v___x_1613_);
v___x_1616_ = v___x_1611_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1613_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_nextMacroScope_1603_);
lean_ctor_set(v_reuseFailAlloc_1633_, 2, v_ngen_1604_);
lean_ctor_set(v_reuseFailAlloc_1633_, 3, v_auxDeclNGen_1605_);
lean_ctor_set(v_reuseFailAlloc_1633_, 4, v_traceState_1606_);
lean_ctor_set(v_reuseFailAlloc_1633_, 5, v___x_1614_);
lean_ctor_set(v_reuseFailAlloc_1633_, 6, v_messages_1607_);
lean_ctor_set(v_reuseFailAlloc_1633_, 7, v_infoState_1608_);
lean_ctor_set(v_reuseFailAlloc_1633_, 8, v_snapshotTasks_1609_);
v___x_1616_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v_mctx_1619_; lean_object* v_zetaDeltaFVarIds_1620_; lean_object* v_postponed_1621_; lean_object* v_diag_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1631_; 
v___x_1617_ = lean_st_ref_set(v___y_1574_, v___x_1616_);
v___x_1618_ = lean_st_ref_take(v___y_1572_);
v_mctx_1619_ = lean_ctor_get(v___x_1618_, 0);
v_zetaDeltaFVarIds_1620_ = lean_ctor_get(v___x_1618_, 2);
v_postponed_1621_ = lean_ctor_get(v___x_1618_, 3);
v_diag_1622_ = lean_ctor_get(v___x_1618_, 4);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1631_ == 0)
{
lean_object* v_unused_1632_; 
v_unused_1632_ = lean_ctor_get(v___x_1618_, 1);
lean_dec(v_unused_1632_);
v___x_1624_ = v___x_1618_;
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_diag_1622_);
lean_inc(v_postponed_1621_);
lean_inc(v_zetaDeltaFVarIds_1620_);
lean_inc(v_mctx_1619_);
lean_dec(v___x_1618_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1631_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1626_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v___x_1626_);
v___x_1628_ = v___x_1624_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_mctx_1619_);
lean_ctor_set(v_reuseFailAlloc_1630_, 1, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1630_, 2, v_zetaDeltaFVarIds_1620_);
lean_ctor_set(v_reuseFailAlloc_1630_, 3, v_postponed_1621_);
lean_ctor_set(v_reuseFailAlloc_1630_, 4, v_diag_1622_);
v___x_1628_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1629_; 
v___x_1629_ = lean_st_ref_set(v___y_1572_, v___x_1628_);
v___y_1455_ = v___x_1587_;
v___y_1456_ = v___y_1571_;
v___y_1457_ = v___y_1572_;
v___y_1458_ = v___y_1573_;
v___y_1459_ = v___y_1574_;
goto v___jp_1454_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1587_);
lean_dec(v_indName_1448_);
lean_dec(v___x_1446_);
return v___x_1597_;
}
}
}
}
}
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec(v_a_1549_);
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1441_);
v_a_1639_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1577_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1577_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_dec(v_a_1549_);
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1441_);
return v___x_1576_;
}
}
else
{
lean_dec(v_a_1549_);
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1441_);
return v___x_1575_;
}
}
v___jp_1647_:
{
lean_object* v___x_1652_; lean_object* v_env_1653_; uint8_t v___x_1654_; 
v___x_1652_ = lean_st_ref_get(v___y_1651_);
v_env_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc_ref(v_env_1653_);
lean_dec(v___x_1652_);
lean_inc(v_indName_1448_);
v___x_1654_ = l_Lean_isMarkedMeta(v_env_1653_, v_indName_1448_);
if (v___x_1654_ == 0)
{
v___y_1571_ = v___y_1648_;
v___y_1572_ = v___y_1649_;
v___y_1573_ = v___y_1650_;
v___y_1574_ = v___y_1651_;
goto v___jp_1570_;
}
else
{
lean_object* v___x_1655_; lean_object* v_env_1656_; lean_object* v_nextMacroScope_1657_; lean_object* v_ngen_1658_; lean_object* v_auxDeclNGen_1659_; lean_object* v_traceState_1660_; lean_object* v_messages_1661_; lean_object* v_infoState_1662_; lean_object* v_snapshotTasks_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1688_; 
v___x_1655_ = lean_st_ref_take(v___y_1651_);
v_env_1656_ = lean_ctor_get(v___x_1655_, 0);
v_nextMacroScope_1657_ = lean_ctor_get(v___x_1655_, 1);
v_ngen_1658_ = lean_ctor_get(v___x_1655_, 2);
v_auxDeclNGen_1659_ = lean_ctor_get(v___x_1655_, 3);
v_traceState_1660_ = lean_ctor_get(v___x_1655_, 4);
v_messages_1661_ = lean_ctor_get(v___x_1655_, 6);
v_infoState_1662_ = lean_ctor_get(v___x_1655_, 7);
v_snapshotTasks_1663_ = lean_ctor_get(v___x_1655_, 8);
v_isSharedCheck_1688_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v___x_1655_, 5);
lean_dec(v_unused_1689_);
v___x_1665_ = v___x_1655_;
v_isShared_1666_ = v_isSharedCheck_1688_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_snapshotTasks_1663_);
lean_inc(v_infoState_1662_);
lean_inc(v_messages_1661_);
lean_inc(v_traceState_1660_);
lean_inc(v_auxDeclNGen_1659_);
lean_inc(v_ngen_1658_);
lean_inc(v_nextMacroScope_1657_);
lean_inc(v_env_1656_);
lean_dec(v___x_1655_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1688_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1670_; 
lean_inc(v___x_1446_);
v___x_1667_ = l_Lean_markMeta(v_env_1656_, v___x_1446_);
v___x_1668_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 5, v___x_1668_);
lean_ctor_set(v___x_1665_, 0, v___x_1667_);
v___x_1670_ = v___x_1665_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1667_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_nextMacroScope_1657_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_ngen_1658_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_auxDeclNGen_1659_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_traceState_1660_);
lean_ctor_set(v_reuseFailAlloc_1687_, 5, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1687_, 6, v_messages_1661_);
lean_ctor_set(v_reuseFailAlloc_1687_, 7, v_infoState_1662_);
lean_ctor_set(v_reuseFailAlloc_1687_, 8, v_snapshotTasks_1663_);
v___x_1670_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v_mctx_1673_; lean_object* v_zetaDeltaFVarIds_1674_; lean_object* v_postponed_1675_; lean_object* v_diag_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1685_; 
v___x_1671_ = lean_st_ref_set(v___y_1651_, v___x_1670_);
v___x_1672_ = lean_st_ref_take(v___y_1649_);
v_mctx_1673_ = lean_ctor_get(v___x_1672_, 0);
v_zetaDeltaFVarIds_1674_ = lean_ctor_get(v___x_1672_, 2);
v_postponed_1675_ = lean_ctor_get(v___x_1672_, 3);
v_diag_1676_ = lean_ctor_get(v___x_1672_, 4);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v___x_1672_, 1);
lean_dec(v_unused_1686_);
v___x_1678_ = v___x_1672_;
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_diag_1676_);
lean_inc(v_postponed_1675_);
lean_inc(v_zetaDeltaFVarIds_1674_);
lean_inc(v_mctx_1673_);
lean_dec(v___x_1672_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1685_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1682_; 
v___x_1680_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 1, v___x_1680_);
v___x_1682_ = v___x_1678_;
goto v_reusejp_1681_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_mctx_1673_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1680_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_zetaDeltaFVarIds_1674_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_postponed_1675_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_diag_1676_);
v___x_1682_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1681_;
}
v_reusejp_1681_:
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_st_ref_set(v___y_1649_, v___x_1682_);
v___y_1571_ = v___y_1648_;
v___y_1572_ = v___y_1649_;
v___y_1573_ = v___y_1650_;
v___y_1574_ = v___y_1651_;
goto v___jp_1570_;
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
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec(v_a_1549_);
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1441_);
lean_dec_ref(v_val_1439_);
v_a_1766_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1555_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1555_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1445_);
lean_dec(v_ctors_1444_);
lean_dec_ref(v___x_1443_);
lean_dec(v___x_1442_);
lean_dec(v___x_1441_);
lean_dec_ref(v___x_1440_);
lean_dec_ref(v_val_1439_);
lean_dec_ref(v_xs_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1434_);
v_a_1774_ = lean_ctor_get(v___x_1548_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1548_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1548_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1548_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec(v_indName_1448_);
lean_dec(v_levelParams_1447_);
lean_dec(v___x_1446_);
lean_dec(v___x_1445_);
lean_dec(v_ctors_1444_);
lean_dec_ref(v___x_1443_);
lean_dec(v___x_1442_);
lean_dec(v___x_1441_);
lean_dec_ref(v___x_1440_);
lean_dec_ref(v_val_1439_);
lean_dec_ref(v_xs_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1434_);
v_a_1782_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1545_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1545_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
v___jp_1454_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1460_ = lean_unsigned_to_nat(1u);
v___x_1461_ = lean_mk_empty_array_with_capacity(v___x_1460_);
lean_inc(v___y_1455_);
v___x_1462_ = lean_array_push(v___x_1461_, v___y_1455_);
v___x_1463_ = l_Lean_compileDecls(v___x_1462_, v___x_1438_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v___x_1464_; lean_object* v_env_1465_; lean_object* v_nextMacroScope_1466_; lean_object* v_ngen_1467_; lean_object* v_auxDeclNGen_1468_; lean_object* v_traceState_1469_; lean_object* v_messages_1470_; lean_object* v_infoState_1471_; lean_object* v_snapshotTasks_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1543_; 
lean_dec_ref_known(v___x_1463_, 1);
v___x_1464_ = lean_st_ref_take(v___y_1459_);
v_env_1465_ = lean_ctor_get(v___x_1464_, 0);
v_nextMacroScope_1466_ = lean_ctor_get(v___x_1464_, 1);
v_ngen_1467_ = lean_ctor_get(v___x_1464_, 2);
v_auxDeclNGen_1468_ = lean_ctor_get(v___x_1464_, 3);
v_traceState_1469_ = lean_ctor_get(v___x_1464_, 4);
v_messages_1470_ = lean_ctor_get(v___x_1464_, 6);
v_infoState_1471_ = lean_ctor_get(v___x_1464_, 7);
v_snapshotTasks_1472_ = lean_ctor_get(v___x_1464_, 8);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1464_, 5);
lean_dec(v_unused_1544_);
v___x_1474_ = v___x_1464_;
v_isShared_1475_ = v_isSharedCheck_1543_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_snapshotTasks_1472_);
lean_inc(v_infoState_1471_);
lean_inc(v_messages_1470_);
lean_inc(v_traceState_1469_);
lean_inc(v_auxDeclNGen_1468_);
lean_inc(v_ngen_1467_);
lean_inc(v_nextMacroScope_1466_);
lean_inc(v_env_1465_);
lean_dec(v___x_1464_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1543_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_inc(v___y_1455_);
v___x_1476_ = l_Lean_Meta_addToCompletionBlackList(v_env_1465_, v___y_1455_);
v___x_1477_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 5, v___x_1477_);
lean_ctor_set(v___x_1474_, 0, v___x_1476_);
v___x_1479_ = v___x_1474_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1476_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_nextMacroScope_1466_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_ngen_1467_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_auxDeclNGen_1468_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_traceState_1469_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1542_, 6, v_messages_1470_);
lean_ctor_set(v_reuseFailAlloc_1542_, 7, v_infoState_1471_);
lean_ctor_set(v_reuseFailAlloc_1542_, 8, v_snapshotTasks_1472_);
v___x_1479_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v_mctx_1482_; lean_object* v_zetaDeltaFVarIds_1483_; lean_object* v_postponed_1484_; lean_object* v_diag_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1540_; 
v___x_1480_ = lean_st_ref_set(v___y_1459_, v___x_1479_);
v___x_1481_ = lean_st_ref_take(v___y_1457_);
v_mctx_1482_ = lean_ctor_get(v___x_1481_, 0);
v_zetaDeltaFVarIds_1483_ = lean_ctor_get(v___x_1481_, 2);
v_postponed_1484_ = lean_ctor_get(v___x_1481_, 3);
v_diag_1485_ = lean_ctor_get(v___x_1481_, 4);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v___x_1481_, 1);
lean_dec(v_unused_1541_);
v___x_1487_ = v___x_1481_;
v_isShared_1488_ = v_isSharedCheck_1540_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_diag_1485_);
lean_inc(v_postponed_1484_);
lean_inc(v_zetaDeltaFVarIds_1483_);
lean_inc(v_mctx_1482_);
lean_dec(v___x_1481_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1540_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1489_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_mctx_1482_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_zetaDeltaFVarIds_1483_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_postponed_1484_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_diag_1485_);
v___x_1491_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v_env_1494_; lean_object* v_nextMacroScope_1495_; lean_object* v_ngen_1496_; lean_object* v_auxDeclNGen_1497_; lean_object* v_traceState_1498_; lean_object* v_messages_1499_; lean_object* v_infoState_1500_; lean_object* v_snapshotTasks_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1537_; 
v___x_1492_ = lean_st_ref_set(v___y_1457_, v___x_1491_);
v___x_1493_ = lean_st_ref_take(v___y_1459_);
v_env_1494_ = lean_ctor_get(v___x_1493_, 0);
v_nextMacroScope_1495_ = lean_ctor_get(v___x_1493_, 1);
v_ngen_1496_ = lean_ctor_get(v___x_1493_, 2);
v_auxDeclNGen_1497_ = lean_ctor_get(v___x_1493_, 3);
v_traceState_1498_ = lean_ctor_get(v___x_1493_, 4);
v_messages_1499_ = lean_ctor_get(v___x_1493_, 6);
v_infoState_1500_ = lean_ctor_get(v___x_1493_, 7);
v_snapshotTasks_1501_ = lean_ctor_get(v___x_1493_, 8);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v___x_1493_, 5);
lean_dec(v_unused_1538_);
v___x_1503_ = v___x_1493_;
v_isShared_1504_ = v_isSharedCheck_1537_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snapshotTasks_1501_);
lean_inc(v_infoState_1500_);
lean_inc(v_messages_1499_);
lean_inc(v_traceState_1498_);
lean_inc(v_auxDeclNGen_1497_);
lean_inc(v_ngen_1496_);
lean_inc(v_nextMacroScope_1495_);
lean_inc(v_env_1494_);
lean_dec(v___x_1493_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1537_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v___x_1505_; lean_object* v___x_1507_; 
lean_inc(v___y_1455_);
v___x_1505_ = l_Lean_addProtected(v_env_1494_, v___y_1455_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 5, v___x_1477_);
lean_ctor_set(v___x_1503_, 0, v___x_1505_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_nextMacroScope_1495_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_ngen_1496_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_auxDeclNGen_1497_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_traceState_1498_);
lean_ctor_set(v_reuseFailAlloc_1536_, 5, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1536_, 6, v_messages_1499_);
lean_ctor_set(v_reuseFailAlloc_1536_, 7, v_infoState_1500_);
lean_ctor_set(v_reuseFailAlloc_1536_, 8, v_snapshotTasks_1501_);
v___x_1507_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_mctx_1510_; lean_object* v_zetaDeltaFVarIds_1511_; lean_object* v_postponed_1512_; lean_object* v_diag_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1534_; 
v___x_1508_ = lean_st_ref_set(v___y_1459_, v___x_1507_);
v___x_1509_ = lean_st_ref_take(v___y_1457_);
v_mctx_1510_ = lean_ctor_get(v___x_1509_, 0);
v_zetaDeltaFVarIds_1511_ = lean_ctor_get(v___x_1509_, 2);
v_postponed_1512_ = lean_ctor_get(v___x_1509_, 3);
v_diag_1513_ = lean_ctor_get(v___x_1509_, 4);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1534_ == 0)
{
lean_object* v_unused_1535_; 
v_unused_1535_ = lean_ctor_get(v___x_1509_, 1);
lean_dec(v_unused_1535_);
v___x_1515_ = v___x_1509_;
v_isShared_1516_ = v_isSharedCheck_1534_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_diag_1513_);
lean_inc(v_postponed_1512_);
lean_inc(v_zetaDeltaFVarIds_1511_);
lean_inc(v_mctx_1510_);
lean_dec(v___x_1509_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1534_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1518_; 
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1489_);
v___x_1518_ = v___x_1515_;
goto v_reusejp_1517_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_mctx_1510_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_zetaDeltaFVarIds_1511_);
lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_postponed_1512_);
lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_diag_1513_);
v___x_1518_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1517_;
}
v_reusejp_1517_:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1531_; 
v___x_1519_ = lean_st_ref_set(v___y_1457_, v___x_1518_);
lean_inc(v___y_1455_);
v___x_1520_ = l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1531_ == 0)
{
lean_object* v_unused_1532_; 
v_unused_1532_ = lean_ctor_get(v___x_1520_, 0);
lean_dec(v_unused_1532_);
v___x_1522_ = v___x_1520_;
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
else
{
lean_dec(v___x_1520_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1531_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
lean_ctor_set_tag(v___x_1522_, 1);
lean_ctor_set(v___x_1522_, 0, v___x_1446_);
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v___x_1446_);
v___x_1525_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1526_ = lean_box(0);
v___x_1527_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_1528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1525_);
lean_ctor_set(v___x_1528_, 1, v___x_1526_);
lean_ctor_set(v___x_1528_, 2, v___x_1527_);
v___x_1529_ = l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(v___y_1455_, v___x_1528_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
return v___x_1529_;
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
lean_dec(v___y_1455_);
lean_dec(v___x_1446_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1790_ = _args[0];
lean_object* v___x_1791_ = _args[1];
lean_object* v_xs_1792_ = _args[2];
lean_object* v___x_1793_ = _args[3];
lean_object* v___x_1794_ = _args[4];
lean_object* v_val_1795_ = _args[5];
lean_object* v___x_1796_ = _args[6];
lean_object* v___x_1797_ = _args[7];
lean_object* v___x_1798_ = _args[8];
lean_object* v___x_1799_ = _args[9];
lean_object* v_ctors_1800_ = _args[10];
lean_object* v___x_1801_ = _args[11];
lean_object* v___x_1802_ = _args[12];
lean_object* v_levelParams_1803_ = _args[13];
lean_object* v_indName_1804_ = _args[14];
lean_object* v___y_1805_ = _args[15];
lean_object* v___y_1806_ = _args[16];
lean_object* v___y_1807_ = _args[17];
lean_object* v___y_1808_ = _args[18];
lean_object* v___y_1809_ = _args[19];
_start:
{
uint8_t v___x_36067__boxed_1810_; uint8_t v___x_36068__boxed_1811_; lean_object* v_res_1812_; 
v___x_36067__boxed_1810_ = lean_unbox(v___x_1793_);
v___x_36068__boxed_1811_ = lean_unbox(v___x_1794_);
v_res_1812_ = l_Lean_mkCtorIdx___lam__1(v___x_1790_, v___x_1791_, v_xs_1792_, v___x_36067__boxed_1810_, v___x_36068__boxed_1811_, v_val_1795_, v___x_1796_, v___x_1797_, v___x_1798_, v___x_1799_, v_ctors_1800_, v___x_1801_, v___x_1802_, v_levelParams_1803_, v_indName_1804_, v___y_1805_, v___y_1806_, v___y_1807_, v___y_1808_);
lean_dec(v___y_1808_);
lean_dec_ref(v___y_1807_);
lean_dec(v___y_1806_);
lean_dec_ref(v___y_1805_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(lean_object* v_bs_1813_, lean_object* v_k_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_){
_start:
{
lean_object* v___x_1820_; 
v___x_1820_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1813_, v_k_1814_, v___y_1815_, v___y_1816_, v___y_1817_, v___y_1818_);
if (lean_obj_tag(v___x_1820_) == 0)
{
lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1828_; 
v_a_1821_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1823_ = v___x_1820_;
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_dec(v___x_1820_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1828_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1821_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
v_a_1829_ = lean_ctor_get(v___x_1820_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1820_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1820_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1820_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object* v_bs_1837_, lean_object* v_k_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(v_bs_1837_, v_k_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
lean_dec_ref(v_bs_1837_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(size_t v_sz_1845_, size_t v_i_1846_, lean_object* v_bs_1847_){
_start:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_lt(v_i_1846_, v_sz_1845_);
if (v___x_1848_ == 0)
{
return v_bs_1847_;
}
else
{
lean_object* v_v_1849_; lean_object* v___x_1850_; lean_object* v_bs_x27_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; size_t v___x_1856_; size_t v___x_1857_; lean_object* v___x_1858_; 
v_v_1849_ = lean_array_uget(v_bs_1847_, v_i_1846_);
v___x_1850_ = lean_unsigned_to_nat(0u);
v_bs_x27_1851_ = lean_array_uset(v_bs_1847_, v_i_1846_, v___x_1850_);
v___x_1852_ = l_Lean_Expr_fvarId_x21(v_v_1849_);
lean_dec(v_v_1849_);
v___x_1853_ = 1;
v___x_1854_ = lean_box(v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1852_);
lean_ctor_set(v___x_1855_, 1, v___x_1854_);
v___x_1856_ = ((size_t)1ULL);
v___x_1857_ = lean_usize_add(v_i_1846_, v___x_1856_);
v___x_1858_ = lean_array_uset(v_bs_x27_1851_, v_i_1846_, v___x_1855_);
v_i_1846_ = v___x_1857_;
v_bs_1847_ = v___x_1858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19___boxed(lean_object* v_sz_1860_, lean_object* v_i_1861_, lean_object* v_bs_1862_){
_start:
{
size_t v_sz_boxed_1863_; size_t v_i_boxed_1864_; lean_object* v_res_1865_; 
v_sz_boxed_1863_ = lean_unbox_usize(v_sz_1860_);
lean_dec(v_sz_1860_);
v_i_boxed_1864_ = lean_unbox_usize(v_i_1861_);
lean_dec(v_i_1861_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(v_sz_boxed_1863_, v_i_boxed_1864_, v_bs_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object* v_bs_1866_, lean_object* v_k_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
size_t v_sz_1873_; size_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_sz_1873_ = lean_array_size(v_bs_1866_);
v___x_1874_ = ((size_t)0ULL);
v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(v_sz_1873_, v___x_1874_, v_bs_1866_);
v___x_1876_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(v___x_1875_, v_k_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_);
lean_dec_ref(v___x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object* v_bs_1877_, lean_object* v_k_1878_, lean_object* v___y_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(v_bs_1877_, v_k_1878_, v___y_1879_, v___y_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
lean_dec(v___y_1880_);
lean_dec_ref(v___y_1879_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1888_, lean_object* v_indName_1889_, lean_object* v___x_1890_, lean_object* v___x_1891_, uint8_t v___x_1892_, uint8_t v___x_1893_, lean_object* v_val_1894_, lean_object* v___x_1895_, lean_object* v_ctors_1896_, lean_object* v___x_1897_, lean_object* v_levelParams_1898_, lean_object* v_xs_1899_, lean_object* v_x_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___f_1918_; lean_object* v___x_1919_; 
v___x_1906_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1888_);
lean_inc_ref_n(v_xs_1899_, 3);
v___x_1907_ = l_Array_toSubarray___redArg(v_xs_1899_, v___x_1906_, v_numParams_1888_);
v___x_1908_ = l_Subarray_copy___redArg(v___x_1907_);
v___x_1909_ = lean_array_get_size(v_xs_1899_);
v___x_1910_ = l_Array_toSubarray___redArg(v_xs_1899_, v_numParams_1888_, v___x_1909_);
v___x_1911_ = l_Subarray_copy___redArg(v___x_1910_);
lean_inc(v___x_1890_);
lean_inc(v_indName_1889_);
v___x_1912_ = l_Lean_mkConst(v_indName_1889_, v___x_1890_);
v___x_1913_ = l_Lean_mkAppN(v___x_1912_, v_xs_1899_);
v___x_1914_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1915_ = l_Lean_mkConst(v___x_1914_, v___x_1891_);
v___x_1916_ = lean_box(v___x_1892_);
v___x_1917_ = lean_box(v___x_1893_);
v___f_1918_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1918_, 0, v___x_1913_);
lean_closure_set(v___f_1918_, 1, v___x_1915_);
lean_closure_set(v___f_1918_, 2, v_xs_1899_);
lean_closure_set(v___f_1918_, 3, v___x_1916_);
lean_closure_set(v___f_1918_, 4, v___x_1917_);
lean_closure_set(v___f_1918_, 5, v_val_1894_);
lean_closure_set(v___f_1918_, 6, v___x_1911_);
lean_closure_set(v___f_1918_, 7, v___x_1890_);
lean_closure_set(v___f_1918_, 8, v___x_1895_);
lean_closure_set(v___f_1918_, 9, v___x_1908_);
lean_closure_set(v___f_1918_, 10, v_ctors_1896_);
lean_closure_set(v___f_1918_, 11, v___x_1906_);
lean_closure_set(v___f_1918_, 12, v___x_1897_);
lean_closure_set(v___f_1918_, 13, v_levelParams_1898_);
lean_closure_set(v___f_1918_, 14, v_indName_1889_);
v___x_1919_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(v_xs_1899_, v___f_1918_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1920_ = _args[0];
lean_object* v_indName_1921_ = _args[1];
lean_object* v___x_1922_ = _args[2];
lean_object* v___x_1923_ = _args[3];
lean_object* v___x_1924_ = _args[4];
lean_object* v___x_1925_ = _args[5];
lean_object* v_val_1926_ = _args[6];
lean_object* v___x_1927_ = _args[7];
lean_object* v_ctors_1928_ = _args[8];
lean_object* v___x_1929_ = _args[9];
lean_object* v_levelParams_1930_ = _args[10];
lean_object* v_xs_1931_ = _args[11];
lean_object* v_x_1932_ = _args[12];
lean_object* v___y_1933_ = _args[13];
lean_object* v___y_1934_ = _args[14];
lean_object* v___y_1935_ = _args[15];
lean_object* v___y_1936_ = _args[16];
lean_object* v___y_1937_ = _args[17];
_start:
{
uint8_t v___x_36755__boxed_1938_; uint8_t v___x_36756__boxed_1939_; lean_object* v_res_1940_; 
v___x_36755__boxed_1938_ = lean_unbox(v___x_1924_);
v___x_36756__boxed_1939_ = lean_unbox(v___x_1925_);
v_res_1940_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1920_, v_indName_1921_, v___x_1922_, v___x_1923_, v___x_36755__boxed_1938_, v___x_36756__boxed_1939_, v_val_1926_, v___x_1927_, v_ctors_1928_, v___x_1929_, v_levelParams_1930_, v_xs_1931_, v_x_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_);
lean_dec(v___y_1936_);
lean_dec_ref(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec_ref(v___y_1933_);
lean_dec_ref(v_x_1932_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
if (lean_obj_tag(v_a_1941_) == 0)
{
lean_object* v___x_1943_; 
v___x_1943_ = l_List_reverse___redArg(v_a_1942_);
return v___x_1943_;
}
else
{
lean_object* v_head_1944_; lean_object* v_tail_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1954_; 
v_head_1944_ = lean_ctor_get(v_a_1941_, 0);
v_tail_1945_ = lean_ctor_get(v_a_1941_, 1);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_a_1941_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1947_ = v_a_1941_;
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_tail_1945_);
lean_inc(v_head_1944_);
lean_dec(v_a_1941_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1954_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1949_ = l_Lean_mkLevelParam(v_head_1944_);
if (v_isShared_1948_ == 0)
{
lean_ctor_set(v___x_1947_, 1, v_a_1942_);
lean_ctor_set(v___x_1947_, 0, v___x_1949_);
v___x_1951_ = v___x_1947_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v___x_1949_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_a_1942_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v_a_1941_ = v_tail_1945_;
v_a_1942_ = v___x_1951_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1957_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1958_ = lean_unsigned_to_nat(62u);
v___x_1959_ = lean_unsigned_to_nat(50u);
v___x_1960_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1961_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1962_ = l_mkPanicMessageWithDecl(v___x_1961_, v___x_1960_, v___x_1959_, v___x_1958_, v___x_1957_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1963_, uint8_t v___x_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_options_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_options_1970_ = lean_ctor_get(v___y_1967_, 2);
v___x_1971_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1972_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_options_1970_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec(v_indName_1963_);
v___x_1973_ = lean_box(0);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2061_; 
lean_inc(v_indName_1963_);
v___x_1975_ = l_Lean_mkCtorIdxName(v_indName_1963_);
lean_inc(v___x_1975_);
v___x_1976_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1975_, v___x_1972_, v___y_1968_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_1979_ = v___x_1976_;
v_isShared_1980_ = v_isSharedCheck_2061_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_dec(v___x_1976_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2061_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_unbox(v_a_1977_);
lean_dec(v_a_1977_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_del_object(v___x_1979_);
lean_inc(v_indName_1963_);
v___x_1982_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1963_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
if (lean_obj_tag(v_a_1983_) == 5)
{
lean_object* v_val_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2046_; 
v_val_1984_ = lean_ctor_get(v_a_1983_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_a_1983_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_1986_ = v_a_1983_;
v_isShared_1987_ = v_isSharedCheck_2046_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_val_1984_);
lean_dec(v_a_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2046_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_toConstantVal_1988_; lean_object* v_numParams_1989_; lean_object* v_numIndices_1990_; lean_object* v_ctors_1991_; lean_object* v_levelParams_1992_; lean_object* v_type_1993_; lean_object* v___x_1994_; 
v_toConstantVal_1988_ = lean_ctor_get(v_val_1984_, 0);
v_numParams_1989_ = lean_ctor_get(v_val_1984_, 1);
lean_inc(v_numParams_1989_);
v_numIndices_1990_ = lean_ctor_get(v_val_1984_, 2);
lean_inc(v_numIndices_1990_);
v_ctors_1991_ = lean_ctor_get(v_val_1984_, 4);
lean_inc(v_ctors_1991_);
v_levelParams_1992_ = lean_ctor_get(v_toConstantVal_1988_, 1);
lean_inc(v_levelParams_1992_);
v_type_1993_ = lean_ctor_get(v_toConstantVal_1988_, 2);
lean_inc_ref_n(v_type_1993_, 2);
v___x_1994_ = l_Lean_Meta_isPropFormerType(v_type_1993_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2037_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_1997_ = v___x_1994_;
v_isShared_1998_ = v_isSharedCheck_2037_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2037_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
uint8_t v___x_1999_; 
v___x_1999_ = lean_unbox(v_a_1995_);
lean_dec(v_a_1995_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_del_object(v___x_1997_);
lean_inc(v_indName_1963_);
v___x_2000_ = l_Lean_mkCasesOnName(v_indName_1963_);
lean_inc(v___x_2000_);
v___x_2001_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_2000_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2024_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_2004_ = v___x_2001_;
v_isShared_2005_ = v_isSharedCheck_2024_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2024_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v___x_2006_ = l_List_lengthTR___redArg(v_levelParams_1992_);
v___x_2007_ = l_Lean_ConstantInfo_levelParams(v_a_2002_);
lean_dec(v_a_2002_);
v___x_2008_ = l_List_lengthTR___redArg(v___x_2007_);
lean_dec(v___x_2007_);
v___x_2009_ = lean_nat_dec_lt(v___x_2006_, v___x_2008_);
lean_dec(v___x_2008_);
lean_dec(v___x_2006_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2012_; 
lean_dec(v___x_2000_);
lean_dec_ref(v_type_1993_);
lean_dec(v_levelParams_1992_);
lean_dec(v_ctors_1991_);
lean_dec(v_numIndices_1990_);
lean_dec(v_numParams_1989_);
lean_del_object(v___x_1986_);
lean_dec_ref(v_val_1984_);
lean_dec(v___x_1975_);
lean_dec(v_indName_1963_);
v___x_2010_ = lean_box(0);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2010_);
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2013_; 
v_reuseFailAlloc_2013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
v___x_2012_ = v_reuseFailAlloc_2013_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
return v___x_2012_;
}
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___f_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_del_object(v___x_2004_);
v___x_2014_ = lean_box(0);
lean_inc(v_levelParams_1992_);
v___x_2015_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_1992_, v___x_2014_);
v___x_2016_ = lean_box(v___x_1964_);
v___x_2017_ = lean_box(v___x_1972_);
lean_inc(v_numParams_1989_);
v___f_2018_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_2018_, 0, v_numParams_1989_);
lean_closure_set(v___f_2018_, 1, v_indName_1963_);
lean_closure_set(v___f_2018_, 2, v___x_2015_);
lean_closure_set(v___f_2018_, 3, v___x_2014_);
lean_closure_set(v___f_2018_, 4, v___x_2016_);
lean_closure_set(v___f_2018_, 5, v___x_2017_);
lean_closure_set(v___f_2018_, 6, v_val_1984_);
lean_closure_set(v___f_2018_, 7, v___x_2000_);
lean_closure_set(v___f_2018_, 8, v_ctors_1991_);
lean_closure_set(v___f_2018_, 9, v___x_1975_);
lean_closure_set(v___f_2018_, 10, v_levelParams_1992_);
v___x_2019_ = lean_nat_add(v_numParams_1989_, v_numIndices_1990_);
lean_dec(v_numIndices_1990_);
lean_dec(v_numParams_1989_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set_tag(v___x_1986_, 1);
lean_ctor_set(v___x_1986_, 0, v___x_2019_);
v___x_2021_ = v___x_1986_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2019_);
v___x_2021_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_1993_, v___x_2021_, v___f_2018_, v___x_1964_, v___x_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
return v___x_2022_;
}
}
}
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2032_; 
lean_dec(v___x_2000_);
lean_dec_ref(v_type_1993_);
lean_dec(v_levelParams_1992_);
lean_dec(v_ctors_1991_);
lean_dec(v_numIndices_1990_);
lean_dec(v_numParams_1989_);
lean_del_object(v___x_1986_);
lean_dec_ref(v_val_1984_);
lean_dec(v___x_1975_);
lean_dec(v_indName_1963_);
v_a_2025_ = lean_ctor_get(v___x_2001_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2001_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2027_ = v___x_2001_;
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_a_2025_);
lean_dec(v___x_2001_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2032_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2030_; 
if (v_isShared_2028_ == 0)
{
v___x_2030_ = v___x_2027_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
v___x_2030_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
return v___x_2030_;
}
}
}
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2035_; 
lean_dec_ref(v_type_1993_);
lean_dec(v_levelParams_1992_);
lean_dec(v_ctors_1991_);
lean_dec(v_numIndices_1990_);
lean_dec(v_numParams_1989_);
lean_del_object(v___x_1986_);
lean_dec_ref(v_val_1984_);
lean_dec(v___x_1975_);
lean_dec(v_indName_1963_);
v___x_2033_ = lean_box(0);
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2033_);
v___x_2035_ = v___x_1997_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
else
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2045_; 
lean_dec_ref(v_type_1993_);
lean_dec(v_levelParams_1992_);
lean_dec(v_ctors_1991_);
lean_dec(v_numIndices_1990_);
lean_dec(v_numParams_1989_);
lean_del_object(v___x_1986_);
lean_dec_ref(v_val_1984_);
lean_dec(v___x_1975_);
lean_dec(v_indName_1963_);
v_a_2038_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2040_ = v___x_1994_;
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_1994_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2045_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
if (v_isShared_2041_ == 0)
{
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
return v___x_2043_;
}
}
}
}
}
else
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
lean_dec(v_a_1983_);
lean_dec(v___x_1975_);
lean_dec(v_indName_1963_);
v___x_2047_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_2048_ = l_panic___at___00Lean_mkCtorIdx_spec__13(v___x_2047_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_);
return v___x_2048_;
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v___x_1975_);
lean_dec(v_indName_1963_);
v_a_2049_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_1982_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_1982_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2059_; 
lean_dec(v___x_1975_);
lean_dec(v_indName_1963_);
v___x_2057_ = lean_box(0);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_2057_);
v___x_2059_ = v___x_1979_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v___x_2057_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2062_, lean_object* v___x_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
uint8_t v___x_36868__boxed_2069_; lean_object* v_res_2070_; 
v___x_36868__boxed_2069_ = lean_unbox(v___x_2063_);
v_res_2070_ = l_Lean_mkCtorIdx___lam__3(v_indName_2062_, v___x_36868__boxed_2069_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_2071_, lean_object* v_e_2072_){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___x_2073_ = l_Lean_indentD(v_e_2072_);
v___x_2074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2071_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_2075_, lean_object* v___f_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2075_, v___f_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2082_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2082_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
v_a_2091_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2082_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2082_);
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
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_2099_, lean_object* v___f_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lean_mkCtorIdx___lam__5(v___f_2099_, v___f_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2106_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___f_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___f_2127_; lean_object* v___f_2128_; uint8_t v___x_2129_; 
v___x_2119_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_2120_ = 0;
v___x_2121_ = lean_box(v___x_2120_);
lean_inc_n(v_indName_2113_, 2);
v___f_2122_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2122_, 0, v_indName_2113_);
lean_closure_set(v___f_2122_, 1, v___x_2121_);
v___x_2123_ = l_Lean_MessageData_ofConstName(v_indName_2113_, v___x_2120_);
v___x_2124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2119_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_2126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___f_2127_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2127_, 0, v___x_2126_);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2128_, 0, v___f_2122_);
lean_closure_set(v___f_2128_, 1, v___f_2127_);
v___x_2129_ = l_Lean_isPrivateName(v_indName_2113_);
lean_dec(v_indName_2113_);
if (v___x_2129_ == 0)
{
uint8_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2130_ = 1;
v___x_2131_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v___f_2128_, v___x_2130_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2131_;
}
else
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v___f_2128_, v___x_2120_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___boxed(lean_object* v_indName_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_mkCtorIdx(v_indName_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(uint8_t v___x_2140_, lean_object* v___x_2141_, lean_object* v_as_2142_, lean_object* v_as_x27_2143_, lean_object* v_b_2144_, lean_object* v_a_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_2140_, v___x_2141_, v_as_x27_2143_, v_b_2144_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___boxed(lean_object* v___x_2152_, lean_object* v___x_2153_, lean_object* v_as_2154_, lean_object* v_as_x27_2155_, lean_object* v_b_2156_, lean_object* v_a_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_){
_start:
{
uint8_t v___x_37175__boxed_2163_; lean_object* v_res_2164_; 
v___x_37175__boxed_2163_ = lean_unbox(v___x_2152_);
v_res_2164_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_37175__boxed_2163_, v___x_2153_, v_as_2154_, v_as_x27_2155_, v_b_2156_, v_a_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v_as_x27_2155_);
lean_dec(v_as_2154_);
lean_dec_ref(v___x_2153_);
return v_res_2164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(lean_object* v_00_u03b1_2165_, lean_object* v_name_2166_, uint8_t v_bi_2167_, lean_object* v_type_2168_, lean_object* v_k_2169_, uint8_t v_kind_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_2166_, v_bi_2167_, v_type_2168_, v_k_2169_, v_kind_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___boxed(lean_object* v_00_u03b1_2177_, lean_object* v_name_2178_, lean_object* v_bi_2179_, lean_object* v_type_2180_, lean_object* v_k_2181_, lean_object* v_kind_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
uint8_t v_bi_boxed_2188_; uint8_t v_kind_boxed_2189_; lean_object* v_res_2190_; 
v_bi_boxed_2188_ = lean_unbox(v_bi_2179_);
v_kind_boxed_2189_ = lean_unbox(v_kind_2182_);
v_res_2190_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10(v_00_u03b1_2177_, v_name_2178_, v_bi_boxed_2188_, v_type_2180_, v_k_2181_, v_kind_boxed_2189_, v___y_2183_, v___y_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
lean_dec(v___y_2184_);
lean_dec_ref(v___y_2183_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(lean_object* v_00_u03b1_2191_, lean_object* v_name_2192_, lean_object* v_type_2193_, lean_object* v_k_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_2192_, v_type_2193_, v_k_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___boxed(lean_object* v_00_u03b1_2201_, lean_object* v_name_2202_, lean_object* v_type_2203_, lean_object* v_k_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7(v_00_u03b1_2201_, v_name_2202_, v_type_2203_, v_k_2204_, v___y_2205_, v___y_2206_, v___y_2207_, v___y_2208_);
lean_dec(v___y_2208_);
lean_dec_ref(v___y_2207_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15(lean_object* v_declName_2211_, uint8_t v_s_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(v_declName_2211_, v_s_2212_, v___y_2214_, v___y_2216_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___boxed(lean_object* v_declName_2219_, lean_object* v_s_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
uint8_t v_s_boxed_2226_; lean_object* v_res_2227_; 
v_s_boxed_2226_ = lean_unbox(v_s_2220_);
v_res_2227_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15(v_declName_2219_, v_s_boxed_2226_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
lean_dec(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17(lean_object* v_env_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(v_env_2228_, v___y_2230_, v___y_2232_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___boxed(lean_object* v_env_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17(v_env_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20(lean_object* v_00_u03b1_2242_, lean_object* v_bs_2243_, lean_object* v_k_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v___x_2250_; 
v___x_2250_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(v_bs_2243_, v_k_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___boxed(lean_object* v_00_u03b1_2251_, lean_object* v_bs_2252_, lean_object* v_k_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20(v_00_u03b1_2251_, v_bs_2252_, v_k_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_bs_2252_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12(lean_object* v_00_u03b1_2260_, lean_object* v_bs_2261_, lean_object* v_k_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v___x_2268_; 
v___x_2268_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(v_bs_2261_, v_k_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___boxed(lean_object* v_00_u03b1_2269_, lean_object* v_bs_2270_, lean_object* v_k_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12(v_00_u03b1_2269_, v_bs_2270_, v_k_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(lean_object* v_00_u03b1_2278_, lean_object* v_constName_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_){
_start:
{
lean_object* v___x_2285_; 
v___x_2285_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___boxed(lean_object* v_00_u03b1_2286_, lean_object* v_constName_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2(v_00_u03b1_2286_, v_constName_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(lean_object* v_00_u03b1_2294_, lean_object* v_msg_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2302_, lean_object* v_msg_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5(v_00_u03b1_2302_, v_msg_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(lean_object* v_00_u03b1_2310_, lean_object* v_ref_2311_, lean_object* v_constName_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_2311_, v_constName_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2319_, lean_object* v_ref_2320_, lean_object* v_constName_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_){
_start:
{
lean_object* v_res_2327_; 
v_res_2327_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7(v_00_u03b1_2319_, v_ref_2320_, v_constName_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v_ref_2320_);
return v_res_2327_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21(lean_object* v_00_u03b1_2328_, lean_object* v_ref_2329_, lean_object* v_msg_2330_, lean_object* v_declHint_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_2329_, v_msg_2330_, v_declHint_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___boxed(lean_object* v_00_u03b1_2338_, lean_object* v_ref_2339_, lean_object* v_msg_2340_, lean_object* v_declHint_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21(v_00_u03b1_2338_, v_ref_2339_, v_msg_2340_, v_declHint_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec_ref(v___y_2342_);
lean_dec(v_ref_2339_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(lean_object* v_msg_2348_, lean_object* v_declHint_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v___x_2355_; 
v___x_2355_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_2348_, v_declHint_2349_, v___y_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___boxed(lean_object* v_msg_2356_, lean_object* v_declHint_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27(v_msg_2356_, v_declHint_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(lean_object* v_00_u03b1_2364_, lean_object* v_ref_2365_, lean_object* v_msg_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_2365_, v_msg_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___boxed(lean_object* v_00_u03b1_2373_, lean_object* v_ref_2374_, lean_object* v_msg_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27(v_00_u03b1_2373_, v_ref_2374_, v_msg_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
lean_dec(v___y_2379_);
lean_dec_ref(v___y_2378_);
lean_dec(v___y_2377_);
lean_dec_ref(v___y_2376_);
lean_dec(v_ref_2374_);
return v_res_2381_;
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
