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
lean_object* v___x_386_; lean_object* v_env_387_; uint8_t v_isExporting_388_; lean_object* v___x_454_; uint8_t v_isModule_455_; 
v___x_386_ = lean_st_ref_get(v___y_384_);
v_env_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc_ref(v_env_387_);
lean_dec(v___x_386_);
v_isExporting_388_ = lean_ctor_get_uint8(v_env_387_, sizeof(void*)*8);
v___x_454_ = l_Lean_Environment_header(v_env_387_);
lean_dec_ref(v_env_387_);
v_isModule_455_ = lean_ctor_get_uint8(v___x_454_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_454_);
if (v_isModule_455_ == 0)
{
lean_object* v___x_456_; 
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
v___x_456_ = lean_apply_5(v_x_379_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, lean_box(0));
return v___x_456_;
}
else
{
if (v_isExporting_388_ == 0)
{
if (v_isExporting_380_ == 0)
{
lean_object* v___x_457_; 
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
v___x_457_ = lean_apply_5(v_x_379_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, lean_box(0));
return v___x_457_;
}
else
{
goto v___jp_389_;
}
}
else
{
if (v_isExporting_380_ == 0)
{
goto v___jp_389_;
}
else
{
lean_object* v___x_458_; 
lean_inc(v___y_384_);
lean_inc_ref(v___y_383_);
lean_inc(v___y_382_);
lean_inc_ref(v___y_381_);
v___x_458_ = lean_apply_5(v_x_379_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, lean_box(0));
return v___x_458_;
}
}
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
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___boxed(lean_object* v_x_459_, lean_object* v_isExporting_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
uint8_t v_isExporting_boxed_466_; lean_object* v_res_467_; 
v_isExporting_boxed_466_ = lean_unbox(v_isExporting_460_);
v_res_467_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v_x_459_, v_isExporting_boxed_466_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14(lean_object* v_00_u03b1_468_, lean_object* v_x_469_, uint8_t v_isExporting_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v_x_469_, v_isExporting_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___boxed(lean_object* v_00_u03b1_477_, lean_object* v_x_478_, lean_object* v_isExporting_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
uint8_t v_isExporting_boxed_485_; lean_object* v_res_486_; 
v_isExporting_boxed_485_ = lean_unbox(v_isExporting_479_);
v_res_486_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14(v_00_u03b1_477_, v_x_478_, v_isExporting_boxed_485_, v___y_480_, v___y_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec(v___y_481_);
lean_dec_ref(v___y_480_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(lean_object* v_cidx_487_, uint8_t v___x_488_, uint8_t v___x_489_, uint8_t v___x_490_, lean_object* v_ys_491_, lean_object* v_x_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = l_Lean_mkRawNatLit(v_cidx_487_);
v___x_499_ = l_Lean_Meta_mkLambdaFVars(v_ys_491_, v___x_498_, v___x_488_, v___x_489_, v___x_488_, v___x_489_, v___x_490_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed(lean_object* v_cidx_500_, lean_object* v___x_501_, lean_object* v___x_502_, lean_object* v___x_503_, lean_object* v_ys_504_, lean_object* v_x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v___x_34522__boxed_511_; uint8_t v___x_34523__boxed_512_; uint8_t v___x_34524__boxed_513_; lean_object* v_res_514_; 
v___x_34522__boxed_511_ = lean_unbox(v___x_501_);
v___x_34523__boxed_512_ = lean_unbox(v___x_502_);
v___x_34524__boxed_513_ = lean_unbox(v___x_503_);
v_res_514_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0(v_cidx_500_, v___x_34522__boxed_511_, v___x_34523__boxed_512_, v___x_34524__boxed_513_, v_ys_504_, v_x_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v_x_505_);
lean_dec_ref(v_ys_504_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(lean_object* v_msgData_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v___x_521_; lean_object* v_env_522_; lean_object* v___x_523_; lean_object* v_mctx_524_; lean_object* v_lctx_525_; lean_object* v_options_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_521_ = lean_st_ref_get(v___y_519_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
lean_inc_ref(v_env_522_);
lean_dec(v___x_521_);
v___x_523_ = lean_st_ref_get(v___y_517_);
v_mctx_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc_ref(v_mctx_524_);
lean_dec(v___x_523_);
v_lctx_525_ = lean_ctor_get(v___y_516_, 2);
v_options_526_ = lean_ctor_get(v___y_518_, 2);
lean_inc_ref(v_options_526_);
lean_inc_ref(v_lctx_525_);
v___x_527_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_527_, 0, v_env_522_);
lean_ctor_set(v___x_527_, 1, v_mctx_524_);
lean_ctor_set(v___x_527_, 2, v_lctx_525_);
lean_ctor_set(v___x_527_, 3, v_options_526_);
v___x_528_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v_msgData_515_);
v___x_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
return v___x_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11___boxed(lean_object* v_msgData_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msgData_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(lean_object* v_msg_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_ref_543_; lean_object* v___x_544_; lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_553_; 
v_ref_543_ = lean_ctor_get(v___y_540_, 5);
v___x_544_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5_spec__11(v_msg_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
v_a_545_ = lean_ctor_get(v___x_544_, 0);
v_isSharedCheck_553_ = !lean_is_exclusive(v___x_544_);
if (v_isSharedCheck_553_ == 0)
{
v___x_547_ = v___x_544_;
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_544_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_553_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_551_; 
lean_inc(v_ref_543_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v_ref_543_);
lean_ctor_set(v___x_549_, 1, v_a_545_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 1);
lean_ctor_set(v___x_547_, 0, v___x_549_);
v___x_551_ = v___x_547_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_549_);
v___x_551_ = v_reuseFailAlloc_552_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg___boxed(lean_object* v_msg_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_560_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0(void){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_instMonadEIO(lean_box(0));
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(lean_object* v_msg_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v_toApplicative_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_635_; 
v___x_572_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0, &l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0_once, _init_l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__0);
v___x_573_ = l_StateRefT_x27_instMonad___redArg(v___x_572_);
v_toApplicative_574_ = lean_ctor_get(v___x_573_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_573_);
if (v_isSharedCheck_635_ == 0)
{
lean_object* v_unused_636_; 
v_unused_636_ = lean_ctor_get(v___x_573_, 1);
lean_dec(v_unused_636_);
v___x_576_ = v___x_573_;
v_isShared_577_ = v_isSharedCheck_635_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_toApplicative_574_);
lean_dec(v___x_573_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_635_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v_toFunctor_578_; lean_object* v_toSeq_579_; lean_object* v_toSeqLeft_580_; lean_object* v_toSeqRight_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_633_; 
v_toFunctor_578_ = lean_ctor_get(v_toApplicative_574_, 0);
v_toSeq_579_ = lean_ctor_get(v_toApplicative_574_, 2);
v_toSeqLeft_580_ = lean_ctor_get(v_toApplicative_574_, 3);
v_toSeqRight_581_ = lean_ctor_get(v_toApplicative_574_, 4);
v_isSharedCheck_633_ = !lean_is_exclusive(v_toApplicative_574_);
if (v_isSharedCheck_633_ == 0)
{
lean_object* v_unused_634_; 
v_unused_634_ = lean_ctor_get(v_toApplicative_574_, 1);
lean_dec(v_unused_634_);
v___x_583_ = v_toApplicative_574_;
v_isShared_584_ = v_isSharedCheck_633_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_toSeqRight_581_);
lean_inc(v_toSeqLeft_580_);
lean_inc(v_toSeq_579_);
lean_inc(v_toFunctor_578_);
lean_dec(v_toApplicative_574_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_633_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___f_585_; lean_object* v___f_586_; lean_object* v___f_587_; lean_object* v___f_588_; lean_object* v___x_589_; lean_object* v___f_590_; lean_object* v___f_591_; lean_object* v___f_592_; lean_object* v___x_594_; 
v___f_585_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__1));
v___f_586_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__2));
lean_inc_ref(v_toFunctor_578_);
v___f_587_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_587_, 0, v_toFunctor_578_);
v___f_588_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_588_, 0, v_toFunctor_578_);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___f_587_);
lean_ctor_set(v___x_589_, 1, v___f_588_);
v___f_590_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_590_, 0, v_toSeqRight_581_);
v___f_591_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_591_, 0, v_toSeqLeft_580_);
v___f_592_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_592_, 0, v_toSeq_579_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 4, v___f_590_);
lean_ctor_set(v___x_583_, 3, v___f_591_);
lean_ctor_set(v___x_583_, 2, v___f_592_);
lean_ctor_set(v___x_583_, 1, v___f_585_);
lean_ctor_set(v___x_583_, 0, v___x_589_);
v___x_594_ = v___x_583_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_589_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___f_585_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v___f_592_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v___f_591_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v___f_590_);
v___x_594_ = v_reuseFailAlloc_632_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 1, v___f_586_);
lean_ctor_set(v___x_576_, 0, v___x_594_);
v___x_596_ = v___x_576_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___f_586_);
v___x_596_ = v_reuseFailAlloc_631_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v_toApplicative_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_629_; 
v___x_597_ = l_StateRefT_x27_instMonad___redArg(v___x_596_);
v_toApplicative_598_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_597_, 1);
lean_dec(v_unused_630_);
v___x_600_ = v___x_597_;
v_isShared_601_ = v_isSharedCheck_629_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_toApplicative_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_629_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_toFunctor_602_; lean_object* v_toSeq_603_; lean_object* v_toSeqLeft_604_; lean_object* v_toSeqRight_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_627_; 
v_toFunctor_602_ = lean_ctor_get(v_toApplicative_598_, 0);
v_toSeq_603_ = lean_ctor_get(v_toApplicative_598_, 2);
v_toSeqLeft_604_ = lean_ctor_get(v_toApplicative_598_, 3);
v_toSeqRight_605_ = lean_ctor_get(v_toApplicative_598_, 4);
v_isSharedCheck_627_ = !lean_is_exclusive(v_toApplicative_598_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v_toApplicative_598_, 1);
lean_dec(v_unused_628_);
v___x_607_ = v_toApplicative_598_;
v_isShared_608_ = v_isSharedCheck_627_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_toSeqRight_605_);
lean_inc(v_toSeqLeft_604_);
lean_inc(v_toSeq_603_);
lean_inc(v_toFunctor_602_);
lean_dec(v_toApplicative_598_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_627_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___f_609_; lean_object* v___f_610_; lean_object* v___f_611_; lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v___f_614_; lean_object* v___f_615_; lean_object* v___f_616_; lean_object* v___x_618_; 
v___f_609_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__3));
v___f_610_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___closed__4));
lean_inc_ref(v_toFunctor_602_);
v___f_611_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_611_, 0, v_toFunctor_602_);
v___f_612_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_612_, 0, v_toFunctor_602_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___f_611_);
lean_ctor_set(v___x_613_, 1, v___f_612_);
v___f_614_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_614_, 0, v_toSeqRight_605_);
v___f_615_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_615_, 0, v_toSeqLeft_604_);
v___f_616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_616_, 0, v_toSeq_603_);
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 4, v___f_614_);
lean_ctor_set(v___x_607_, 3, v___f_615_);
lean_ctor_set(v___x_607_, 2, v___f_616_);
lean_ctor_set(v___x_607_, 1, v___f_609_);
lean_ctor_set(v___x_607_, 0, v___x_613_);
v___x_618_ = v___x_607_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v___f_609_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v___f_616_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v___f_615_);
lean_ctor_set(v_reuseFailAlloc_626_, 4, v___f_614_);
v___x_618_ = v_reuseFailAlloc_626_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_620_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v___f_610_);
lean_ctor_set(v___x_600_, 0, v___x_618_);
v___x_620_ = v___x_600_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v___f_610_);
v___x_620_ = v_reuseFailAlloc_625_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_30029__overap_623_; lean_object* v___x_624_; 
v___x_621_ = lean_box(0);
v___x_622_ = l_instInhabitedOfMonad___redArg(v___x_620_, v___x_621_);
v___x_30029__overap_623_ = lean_panic_fn_borrowed(v___x_622_, v_msg_566_);
lean_dec(v___x_622_);
lean_inc(v___y_570_);
lean_inc_ref(v___y_569_);
lean_inc(v___y_568_);
lean_inc_ref(v___y_567_);
v___x_624_ = lean_apply_5(v___x_30029__overap_623_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, lean_box(0));
return v___x_624_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6___boxed(lean_object* v_msg_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v_msg_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
return v_res_643_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__0));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__2));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_654_ = lean_unsigned_to_nat(11u);
v___x_655_ = lean_unsigned_to_nat(122u);
v___x_656_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__5));
v___x_657_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__4));
v___x_658_ = l_mkPanicMessageWithDecl(v___x_657_, v___x_656_, v___x_655_, v___x_654_, v___x_653_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(lean_object* v_constName_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_673_; lean_object* v_env_674_; uint8_t v___x_675_; lean_object* v___x_676_; 
v___x_673_ = lean_st_ref_get(v___y_663_);
v_env_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc_ref(v_env_674_);
lean_dec(v___x_673_);
v___x_675_ = 0;
lean_inc(v_constName_659_);
v___x_676_ = l_Lean_Environment_findAsync_x3f(v_env_674_, v_constName_659_, v___x_675_);
if (lean_obj_tag(v___x_676_) == 1)
{
lean_object* v_val_677_; uint8_t v_kind_678_; 
v_val_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v___x_676_, 1);
v_kind_678_ = lean_ctor_get_uint8(v_val_677_, sizeof(void*)*3);
if (v_kind_678_ == 6)
{
lean_object* v___x_679_; 
v___x_679_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_677_);
if (lean_obj_tag(v___x_679_) == 6)
{
lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_constName_659_);
v_val_680_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_679_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v___x_679_);
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
else
{
lean_object* v___x_688_; lean_object* v___x_689_; 
lean_dec_ref(v___x_679_);
v___x_688_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__7);
v___x_689_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__6(v___x_688_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_698_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
if (lean_obj_tag(v_a_690_) == 0)
{
lean_del_object(v___x_692_);
goto v___jp_665_;
}
else
{
lean_object* v_val_694_; lean_object* v___x_696_; 
lean_dec(v_constName_659_);
v_val_694_ = lean_ctor_get(v_a_690_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v_a_690_, 1);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v_val_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_val_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec(v_constName_659_);
v_a_699_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_689_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_689_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
else
{
lean_dec(v_val_677_);
goto v___jp_665_;
}
}
else
{
lean_dec(v___x_676_);
goto v___jp_665_;
}
v___jp_665_:
{
lean_object* v___x_666_; uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_666_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_667_ = 0;
v___x_668_ = l_Lean_MessageData_ofConstName(v_constName_659_, v___x_667_);
v___x_669_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_666_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__3);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_671_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___boxed(lean_object* v_constName_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_constName_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(uint8_t v___x_714_, lean_object* v___x_715_, lean_object* v_as_x27_716_, lean_object* v_b_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_){
_start:
{
if (lean_obj_tag(v_as_x27_716_) == 0)
{
lean_object* v___x_723_; 
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v_b_717_);
return v___x_723_;
}
else
{
lean_object* v_head_724_; lean_object* v_tail_725_; lean_object* v___x_726_; 
v_head_724_ = lean_ctor_get(v_as_x27_716_, 0);
v_tail_725_ = lean_ctor_get(v_as_x27_716_, 1);
lean_inc(v_head_724_);
v___x_726_ = l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4(v_head_724_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v_toConstantVal_728_; lean_object* v_cidx_729_; lean_object* v_numFields_730_; lean_object* v_type_731_; lean_object* v___x_732_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v_toConstantVal_728_ = lean_ctor_get(v_a_727_, 0);
lean_inc_ref(v_toConstantVal_728_);
v_cidx_729_ = lean_ctor_get(v_a_727_, 2);
lean_inc(v_cidx_729_);
v_numFields_730_ = lean_ctor_get(v_a_727_, 4);
lean_inc(v_numFields_730_);
lean_dec(v_a_727_);
v_type_731_ = lean_ctor_get(v_toConstantVal_728_, 2);
lean_inc_ref(v_type_731_);
lean_dec_ref(v_toConstantVal_728_);
v___x_732_ = l_Lean_Meta_instantiateForall(v_type_731_, v___x_715_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_750_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_750_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_750_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_750_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
uint8_t v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___x_744_; 
v___x_737_ = 0;
v___x_738_ = 1;
v___x_739_ = lean_box(v___x_737_);
v___x_740_ = lean_box(v___x_714_);
v___x_741_ = lean_box(v___x_738_);
v___f_742_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___lam__0___boxed), 11, 4);
lean_closure_set(v___f_742_, 0, v_cidx_729_);
lean_closure_set(v___f_742_, 1, v___x_739_);
lean_closure_set(v___f_742_, 2, v___x_740_);
lean_closure_set(v___f_742_, 3, v___x_741_);
if (v_isShared_736_ == 0)
{
lean_ctor_set_tag(v___x_735_, 1);
lean_ctor_set(v___x_735_, 0, v_numFields_730_);
v___x_744_ = v___x_735_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_numFields_730_);
v___x_744_ = v_reuseFailAlloc_749_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; 
v___x_745_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_a_733_, v___x_744_, v___f_742_, v___x_737_, v___x_737_, v___y_718_, v___y_719_, v___y_720_, v___y_721_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v_a_746_; lean_object* v___x_747_; 
v_a_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_a_746_);
lean_dec_ref_known(v___x_745_, 1);
v___x_747_ = l_Lean_Expr_app___override(v_b_717_, v_a_746_);
v_as_x27_716_ = v_tail_725_;
v_b_717_ = v___x_747_;
goto _start;
}
else
{
lean_dec_ref(v_b_717_);
return v___x_745_;
}
}
}
}
else
{
lean_dec(v_numFields_730_);
lean_dec(v_cidx_729_);
lean_dec_ref(v_b_717_);
return v___x_732_;
}
}
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v_b_717_);
v_a_751_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_726_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_726_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg___boxed(lean_object* v___x_759_, lean_object* v___x_760_, lean_object* v_as_x27_761_, lean_object* v_b_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
uint8_t v___x_34894__boxed_768_; lean_object* v_res_769_; 
v___x_34894__boxed_768_ = lean_unbox(v___x_759_);
v_res_769_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_34894__boxed_768_, v___x_760_, v_as_x27_761_, v_b_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v_as_x27_761_);
lean_dec_ref(v___x_760_);
return v_res_769_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__0___closed__0(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = lean_box(0);
v___x_771_ = l_Lean_Level_succ___override(v___x_770_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0(lean_object* v_xs_772_, uint8_t v___x_773_, uint8_t v___x_774_, uint8_t v___x_775_, lean_object* v_val_776_, lean_object* v___x_777_, lean_object* v___x_778_, lean_object* v___x_779_, lean_object* v___x_780_, lean_object* v___x_781_, lean_object* v_ctors_782_, lean_object* v___x_783_, lean_object* v_x_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_value_791_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v___x_794_ = l_Lean_InductiveVal_numCtors(v_val_776_);
v___x_795_ = lean_unsigned_to_nat(1u);
v___x_796_ = lean_nat_dec_eq(v___x_794_, v___x_795_);
lean_dec(v___x_794_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec(v___x_783_);
lean_inc_ref(v_x_784_);
lean_inc_ref(v___x_777_);
v___x_797_ = lean_array_push(v___x_777_, v_x_784_);
v___x_798_ = l_Lean_Meta_mkLambdaFVars(v___x_797_, v___x_778_, v___x_773_, v___x_774_, v___x_773_, v___x_774_, v___x_775_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec_ref(v___x_797_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__0___closed__0, &l_Lean_mkCtorIdx___lam__0___closed__0_once, _init_l_Lean_mkCtorIdx___lam__0___closed__0);
v___x_801_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
lean_ctor_set(v___x_801_, 1, v___x_779_);
v___x_802_ = l_Lean_mkConst(v___x_780_, v___x_801_);
v___x_803_ = l_Lean_mkAppN(v___x_802_, v___x_781_);
v___x_804_ = l_Lean_Expr_app___override(v___x_803_, v_a_799_);
v___x_805_ = l_Lean_mkAppN(v___x_804_, v___x_777_);
lean_dec_ref(v___x_777_);
lean_inc_ref(v_x_784_);
v___x_806_ = l_Lean_Expr_app___override(v___x_805_, v_x_784_);
v___x_807_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6___redArg(v___x_774_, v___x_781_, v_ctors_782_, v___x_806_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v_value_791_ = v_a_808_;
goto v___jp_790_;
}
else
{
lean_dec_ref(v_x_784_);
lean_dec_ref(v_xs_772_);
return v___x_807_;
}
}
else
{
lean_dec_ref(v_x_784_);
lean_dec(v___x_780_);
lean_dec(v___x_779_);
lean_dec_ref(v___x_777_);
lean_dec_ref(v_xs_772_);
return v___x_798_;
}
}
else
{
lean_object* v___x_809_; 
lean_dec(v___x_780_);
lean_dec(v___x_779_);
lean_dec_ref(v___x_778_);
lean_dec_ref(v___x_777_);
v___x_809_ = l_Lean_mkRawNatLit(v___x_783_);
v_value_791_ = v___x_809_;
goto v___jp_790_;
}
v___jp_790_:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_array_push(v_xs_772_, v_x_784_);
v___x_793_ = l_Lean_Meta_mkLambdaFVars(v___x_792_, v_value_791_, v___x_773_, v___x_774_, v___x_773_, v___x_774_, v___x_775_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
lean_dec_ref(v___x_792_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__0___boxed(lean_object** _args){
lean_object* v_xs_810_ = _args[0];
lean_object* v___x_811_ = _args[1];
lean_object* v___x_812_ = _args[2];
lean_object* v___x_813_ = _args[3];
lean_object* v_val_814_ = _args[4];
lean_object* v___x_815_ = _args[5];
lean_object* v___x_816_ = _args[6];
lean_object* v___x_817_ = _args[7];
lean_object* v___x_818_ = _args[8];
lean_object* v___x_819_ = _args[9];
lean_object* v_ctors_820_ = _args[10];
lean_object* v___x_821_ = _args[11];
lean_object* v_x_822_ = _args[12];
lean_object* v___y_823_ = _args[13];
lean_object* v___y_824_ = _args[14];
lean_object* v___y_825_ = _args[15];
lean_object* v___y_826_ = _args[16];
lean_object* v___y_827_ = _args[17];
_start:
{
uint8_t v___x_34985__boxed_828_; uint8_t v___x_34986__boxed_829_; uint8_t v___x_34987__boxed_830_; lean_object* v_res_831_; 
v___x_34985__boxed_828_ = lean_unbox(v___x_811_);
v___x_34986__boxed_829_ = lean_unbox(v___x_812_);
v___x_34987__boxed_830_ = lean_unbox(v___x_813_);
v_res_831_ = l_Lean_mkCtorIdx___lam__0(v_xs_810_, v___x_34985__boxed_828_, v___x_34986__boxed_829_, v___x_34987__boxed_830_, v_val_814_, v___x_815_, v___x_816_, v___x_817_, v___x_818_, v___x_819_, v_ctors_820_, v___x_821_, v_x_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec(v_ctors_820_);
lean_dec_ref(v___x_819_);
lean_dec_ref(v_val_814_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(lean_object* v_k_832_, lean_object* v_b_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; 
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
v___x_839_ = lean_apply_6(v_k_832_, v_b_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, lean_box(0));
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed(lean_object* v_k_840_, lean_object* v_b_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0(v_k_840_, v_b_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(lean_object* v_name_848_, uint8_t v_bi_849_, lean_object* v_type_850_, lean_object* v_k_851_, uint8_t v_kind_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___f_858_; lean_object* v___x_859_; 
v___f_858_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_858_, 0, v_k_851_);
v___x_859_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_848_, v_bi_849_, v_type_850_, v___f_858_, v_kind_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_859_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_859_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_859_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_859_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg___boxed(lean_object* v_name_876_, lean_object* v_bi_877_, lean_object* v_type_878_, lean_object* v_k_879_, lean_object* v_kind_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_){
_start:
{
uint8_t v_bi_boxed_886_; uint8_t v_kind_boxed_887_; lean_object* v_res_888_; 
v_bi_boxed_886_ = lean_unbox(v_bi_877_);
v_kind_boxed_887_ = lean_unbox(v_kind_880_);
v_res_888_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_876_, v_bi_boxed_886_, v_type_878_, v_k_879_, v_kind_boxed_887_, v___y_881_, v___y_882_, v___y_883_, v___y_884_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(lean_object* v_name_889_, lean_object* v_type_890_, lean_object* v_k_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; uint8_t v___x_898_; lean_object* v___x_899_; 
v___x_897_ = 0;
v___x_898_ = 0;
v___x_899_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7_spec__10___redArg(v_name_889_, v___x_897_, v_type_890_, v_k_891_, v___x_898_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg___boxed(lean_object* v_name_900_, lean_object* v_type_901_, lean_object* v_k_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v_name_900_, v_type_901_, v_k_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(lean_object* v_declName_909_, uint8_t v_s_910_, lean_object* v___y_911_, lean_object* v___y_912_){
_start:
{
lean_object* v___x_914_; lean_object* v_env_915_; lean_object* v_nextMacroScope_916_; lean_object* v_ngen_917_; lean_object* v_auxDeclNGen_918_; lean_object* v_traceState_919_; lean_object* v_messages_920_; lean_object* v_infoState_921_; lean_object* v_snapshotTasks_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_951_; 
v___x_914_ = lean_st_ref_take(v___y_912_);
v_env_915_ = lean_ctor_get(v___x_914_, 0);
v_nextMacroScope_916_ = lean_ctor_get(v___x_914_, 1);
v_ngen_917_ = lean_ctor_get(v___x_914_, 2);
v_auxDeclNGen_918_ = lean_ctor_get(v___x_914_, 3);
v_traceState_919_ = lean_ctor_get(v___x_914_, 4);
v_messages_920_ = lean_ctor_get(v___x_914_, 6);
v_infoState_921_ = lean_ctor_get(v___x_914_, 7);
v_snapshotTasks_922_ = lean_ctor_get(v___x_914_, 8);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v___x_914_, 5);
lean_dec(v_unused_952_);
v___x_924_ = v___x_914_;
v_isShared_925_ = v_isSharedCheck_951_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_snapshotTasks_922_);
lean_inc(v_infoState_921_);
lean_inc(v_messages_920_);
lean_inc(v_traceState_919_);
lean_inc(v_auxDeclNGen_918_);
lean_inc(v_ngen_917_);
lean_inc(v_nextMacroScope_916_);
lean_inc(v_env_915_);
lean_dec(v___x_914_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_951_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
uint8_t v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_926_ = 0;
v___x_927_ = lean_box(0);
v___x_928_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_915_, v_declName_909_, v_s_910_, v___x_926_, v___x_927_);
v___x_929_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 5, v___x_929_);
lean_ctor_set(v___x_924_, 0, v___x_928_);
v___x_931_ = v___x_924_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_nextMacroScope_916_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_ngen_917_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_auxDeclNGen_918_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_traceState_919_);
lean_ctor_set(v_reuseFailAlloc_950_, 5, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_950_, 6, v_messages_920_);
lean_ctor_set(v_reuseFailAlloc_950_, 7, v_infoState_921_);
lean_ctor_set(v_reuseFailAlloc_950_, 8, v_snapshotTasks_922_);
v___x_931_ = v_reuseFailAlloc_950_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v_mctx_934_; lean_object* v_zetaDeltaFVarIds_935_; lean_object* v_postponed_936_; lean_object* v_diag_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
v___x_932_ = lean_st_ref_set(v___y_912_, v___x_931_);
v___x_933_ = lean_st_ref_take(v___y_911_);
v_mctx_934_ = lean_ctor_get(v___x_933_, 0);
v_zetaDeltaFVarIds_935_ = lean_ctor_get(v___x_933_, 2);
v_postponed_936_ = lean_ctor_get(v___x_933_, 3);
v_diag_937_ = lean_ctor_get(v___x_933_, 4);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_948_ == 0)
{
lean_object* v_unused_949_; 
v_unused_949_ = lean_ctor_get(v___x_933_, 1);
lean_dec(v_unused_949_);
v___x_939_ = v___x_933_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_diag_937_);
lean_inc(v_postponed_936_);
lean_inc(v_zetaDeltaFVarIds_935_);
lean_inc(v_mctx_934_);
lean_dec(v___x_933_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_mctx_934_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_zetaDeltaFVarIds_935_);
lean_ctor_set(v_reuseFailAlloc_947_, 3, v_postponed_936_);
lean_ctor_set(v_reuseFailAlloc_947_, 4, v_diag_937_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_944_ = lean_st_ref_set(v___y_911_, v___x_943_);
v___x_945_ = lean_box(0);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg___boxed(lean_object* v_declName_953_, lean_object* v_s_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_){
_start:
{
uint8_t v_s_boxed_958_; lean_object* v_res_959_; 
v_s_boxed_958_ = lean_unbox(v_s_954_);
v_res_959_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(v_declName_953_, v_s_boxed_958_, v___y_955_, v___y_956_);
lean_dec(v___y_956_);
lean_dec(v___y_955_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(lean_object* v_declName_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
uint8_t v___x_966_; lean_object* v___x_967_; 
v___x_966_ = 0;
v___x_967_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10_spec__15___redArg(v_declName_960_, v___x_966_, v___y_962_, v___y_964_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10___boxed(lean_object* v_declName_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(v_declName_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
return v_res_974_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0(void){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_975_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; 
v___x_976_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__0);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_979_);
lean_ctor_set(v___x_980_, 2, v___x_979_);
lean_ctor_set(v___x_980_, 3, v___x_979_);
lean_ctor_set(v___x_980_, 4, v___x_978_);
lean_ctor_set(v___x_980_, 5, v___x_978_);
lean_ctor_set(v___x_980_, 6, v___x_978_);
lean_ctor_set(v___x_980_, 7, v___x_978_);
lean_ctor_set(v___x_980_, 8, v___x_978_);
lean_ctor_set(v___x_980_, 9, v___x_978_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = lean_unsigned_to_nat(32u);
v___x_982_ = lean_mk_empty_array_with_capacity(v___x_981_);
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4(void){
_start:
{
size_t v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_984_ = ((size_t)5ULL);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_unsigned_to_nat(32u);
v___x_987_ = lean_mk_empty_array_with_capacity(v___x_986_);
v___x_988_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__3);
v___x_989_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_989_, 0, v___x_988_);
lean_ctor_set(v___x_989_, 1, v___x_987_);
lean_ctor_set(v___x_989_, 2, v___x_985_);
lean_ctor_set(v___x_989_, 3, v___x_985_);
lean_ctor_set_usize(v___x_989_, 4, v___x_984_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_990_ = lean_box(1);
v___x_991_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__4);
v___x_992_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__1);
v___x_993_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___x_991_);
lean_ctor_set(v___x_993_, 2, v___x_990_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__6));
v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9(void){
_start:
{
lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_998_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__8));
v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11(void){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__10));
v___x_1002_ = l_Lean_stringToMessageData(v___x_1001_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13(void){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; 
v___x_1004_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__12));
v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
return v___x_1005_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15(void){
_start:
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
v___x_1007_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__14));
v___x_1008_ = l_Lean_stringToMessageData(v___x_1007_);
return v___x_1008_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17(void){
_start:
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__16));
v___x_1011_ = l_Lean_stringToMessageData(v___x_1010_);
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__18));
v___x_1014_ = l_Lean_stringToMessageData(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(lean_object* v_msg_1015_, lean_object* v_declHint_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___x_1019_; lean_object* v_env_1020_; uint8_t v___x_1021_; 
v___x_1019_ = lean_st_ref_get(v___y_1017_);
v_env_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc_ref(v_env_1020_);
lean_dec(v___x_1019_);
v___x_1021_ = l_Lean_Name_isAnonymous(v_declHint_1016_);
if (v___x_1021_ == 0)
{
uint8_t v_isExporting_1022_; 
v_isExporting_1022_ = lean_ctor_get_uint8(v_env_1020_, sizeof(void*)*8);
if (v_isExporting_1022_ == 0)
{
lean_object* v___x_1023_; 
lean_dec_ref(v_env_1020_);
lean_dec(v_declHint_1016_);
v___x_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_msg_1015_);
return v___x_1023_;
}
else
{
lean_object* v___x_1024_; uint8_t v___x_1025_; 
lean_inc_ref(v_env_1020_);
v___x_1024_ = l_Lean_Environment_setExporting(v_env_1020_, v___x_1021_);
lean_inc(v_declHint_1016_);
lean_inc_ref(v___x_1024_);
v___x_1025_ = l_Lean_Environment_contains(v___x_1024_, v_declHint_1016_, v_isExporting_1022_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; 
lean_dec_ref(v___x_1024_);
lean_dec_ref(v_env_1020_);
lean_dec(v_declHint_1016_);
v___x_1026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_msg_1015_);
return v___x_1026_;
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_c_1032_; lean_object* v___x_1033_; 
v___x_1027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__2);
v___x_1028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__5);
v___x_1029_ = l_Lean_Options_empty;
v___x_1030_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1024_);
lean_ctor_set(v___x_1030_, 1, v___x_1027_);
lean_ctor_set(v___x_1030_, 2, v___x_1028_);
lean_ctor_set(v___x_1030_, 3, v___x_1029_);
lean_inc(v_declHint_1016_);
v___x_1031_ = l_Lean_MessageData_ofConstName(v_declHint_1016_, v___x_1021_);
v_c_1032_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1032_, 0, v___x_1030_);
lean_ctor_set(v_c_1032_, 1, v___x_1031_);
v___x_1033_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1020_, v_declHint_1016_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec_ref(v_env_1020_);
lean_dec(v_declHint_1016_);
v___x_1034_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_1035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v_c_1032_);
v___x_1036_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__9);
v___x_1037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1035_);
lean_ctor_set(v___x_1037_, 1, v___x_1036_);
v___x_1038_ = l_Lean_MessageData_note(v___x_1037_);
v___x_1039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1039_, 0, v_msg_1015_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1039_);
return v___x_1040_;
}
else
{
lean_object* v_val_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1076_; 
v_val_1041_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1043_ = v___x_1033_;
v_isShared_1044_ = v_isSharedCheck_1076_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_val_1041_);
lean_dec(v___x_1033_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1076_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v_mod_1048_; uint8_t v___x_1049_; 
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Lean_Environment_header(v_env_1020_);
lean_dec_ref(v_env_1020_);
v___x_1047_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1046_);
v_mod_1048_ = lean_array_get(v___x_1045_, v___x_1047_, v_val_1041_);
lean_dec(v_val_1041_);
lean_dec_ref(v___x_1047_);
v___x_1049_ = l_Lean_isPrivateName(v_declHint_1016_);
lean_dec(v_declHint_1016_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__11);
v___x_1051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
lean_ctor_set(v___x_1051_, 1, v_c_1032_);
v___x_1052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__13);
v___x_1053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1053_, 0, v___x_1051_);
lean_ctor_set(v___x_1053_, 1, v___x_1052_);
v___x_1054_ = l_Lean_MessageData_ofName(v_mod_1048_);
v___x_1055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1053_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1056_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__15);
v___x_1057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1055_);
lean_ctor_set(v___x_1057_, 1, v___x_1056_);
v___x_1058_ = l_Lean_MessageData_note(v___x_1057_);
v___x_1059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1059_, 0, v_msg_1015_);
lean_ctor_set(v___x_1059_, 1, v___x_1058_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1059_);
v___x_1061_ = v___x_1043_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__7);
v___x_1064_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
lean_ctor_set(v___x_1064_, 1, v_c_1032_);
v___x_1065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__17);
v___x_1066_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1064_);
lean_ctor_set(v___x_1066_, 1, v___x_1065_);
v___x_1067_ = l_Lean_MessageData_ofName(v_mod_1048_);
v___x_1068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1066_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___closed__19);
v___x_1070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1068_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v___x_1071_ = l_Lean_MessageData_note(v___x_1070_);
v___x_1072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1072_, 0, v_msg_1015_);
lean_ctor_set(v___x_1072_, 1, v___x_1071_);
if (v_isShared_1044_ == 0)
{
lean_ctor_set_tag(v___x_1043_, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1072_);
v___x_1074_ = v___x_1043_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v___x_1072_);
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
}
}
}
else
{
lean_object* v___x_1077_; 
lean_dec_ref(v_env_1020_);
lean_dec(v_declHint_1016_);
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_msg_1015_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg___boxed(lean_object* v_msg_1078_, lean_object* v_declHint_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_1078_, v_declHint_1079_, v___y_1080_);
lean_dec(v___y_1080_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(lean_object* v_msg_1083_, lean_object* v_declHint_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1090_; lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1100_; 
v___x_1090_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26_spec__27___redArg(v_msg_1083_, v_declHint_1084_, v___y_1088_);
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1100_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1095_ = l_Lean_unknownIdentifierMessageTag;
v___x_1096_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_a_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1096_);
v___x_1098_ = v___x_1093_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26___boxed(lean_object* v_msg_1101_, lean_object* v_declHint_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_1101_, v_declHint_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(lean_object* v_ref_1109_, lean_object* v_msg_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v_fileName_1116_; lean_object* v_fileMap_1117_; lean_object* v_options_1118_; lean_object* v_currRecDepth_1119_; lean_object* v_maxRecDepth_1120_; lean_object* v_ref_1121_; lean_object* v_currNamespace_1122_; lean_object* v_openDecls_1123_; lean_object* v_initHeartbeats_1124_; lean_object* v_maxHeartbeats_1125_; lean_object* v_quotContext_1126_; lean_object* v_currMacroScope_1127_; uint8_t v_diag_1128_; lean_object* v_cancelTk_x3f_1129_; uint8_t v_suppressElabErrors_1130_; lean_object* v_inheritedTraceOptions_1131_; lean_object* v_ref_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v_fileName_1116_ = lean_ctor_get(v___y_1113_, 0);
v_fileMap_1117_ = lean_ctor_get(v___y_1113_, 1);
v_options_1118_ = lean_ctor_get(v___y_1113_, 2);
v_currRecDepth_1119_ = lean_ctor_get(v___y_1113_, 3);
v_maxRecDepth_1120_ = lean_ctor_get(v___y_1113_, 4);
v_ref_1121_ = lean_ctor_get(v___y_1113_, 5);
v_currNamespace_1122_ = lean_ctor_get(v___y_1113_, 6);
v_openDecls_1123_ = lean_ctor_get(v___y_1113_, 7);
v_initHeartbeats_1124_ = lean_ctor_get(v___y_1113_, 8);
v_maxHeartbeats_1125_ = lean_ctor_get(v___y_1113_, 9);
v_quotContext_1126_ = lean_ctor_get(v___y_1113_, 10);
v_currMacroScope_1127_ = lean_ctor_get(v___y_1113_, 11);
v_diag_1128_ = lean_ctor_get_uint8(v___y_1113_, sizeof(void*)*14);
v_cancelTk_x3f_1129_ = lean_ctor_get(v___y_1113_, 12);
v_suppressElabErrors_1130_ = lean_ctor_get_uint8(v___y_1113_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1131_ = lean_ctor_get(v___y_1113_, 13);
v_ref_1132_ = l_Lean_replaceRef(v_ref_1109_, v_ref_1121_);
lean_inc_ref(v_inheritedTraceOptions_1131_);
lean_inc(v_cancelTk_x3f_1129_);
lean_inc(v_currMacroScope_1127_);
lean_inc(v_quotContext_1126_);
lean_inc(v_maxHeartbeats_1125_);
lean_inc(v_initHeartbeats_1124_);
lean_inc(v_openDecls_1123_);
lean_inc(v_currNamespace_1122_);
lean_inc(v_maxRecDepth_1120_);
lean_inc(v_currRecDepth_1119_);
lean_inc_ref(v_options_1118_);
lean_inc_ref(v_fileMap_1117_);
lean_inc_ref(v_fileName_1116_);
v___x_1133_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1133_, 0, v_fileName_1116_);
lean_ctor_set(v___x_1133_, 1, v_fileMap_1117_);
lean_ctor_set(v___x_1133_, 2, v_options_1118_);
lean_ctor_set(v___x_1133_, 3, v_currRecDepth_1119_);
lean_ctor_set(v___x_1133_, 4, v_maxRecDepth_1120_);
lean_ctor_set(v___x_1133_, 5, v_ref_1132_);
lean_ctor_set(v___x_1133_, 6, v_currNamespace_1122_);
lean_ctor_set(v___x_1133_, 7, v_openDecls_1123_);
lean_ctor_set(v___x_1133_, 8, v_initHeartbeats_1124_);
lean_ctor_set(v___x_1133_, 9, v_maxHeartbeats_1125_);
lean_ctor_set(v___x_1133_, 10, v_quotContext_1126_);
lean_ctor_set(v___x_1133_, 11, v_currMacroScope_1127_);
lean_ctor_set(v___x_1133_, 12, v_cancelTk_x3f_1129_);
lean_ctor_set(v___x_1133_, 13, v_inheritedTraceOptions_1131_);
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*14, v_diag_1128_);
lean_ctor_set_uint8(v___x_1133_, sizeof(void*)*14 + 1, v_suppressElabErrors_1130_);
v___x_1134_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v_msg_1110_, v___y_1111_, v___y_1112_, v___x_1133_, v___y_1114_);
lean_dec_ref_known(v___x_1133_, 14);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg___boxed(lean_object* v_ref_1135_, lean_object* v_msg_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_1135_, v_msg_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
lean_dec(v_ref_1135_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(lean_object* v_ref_1143_, lean_object* v_msg_1144_, lean_object* v_declHint_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; lean_object* v_a_1152_; lean_object* v___x_1153_; 
v___x_1151_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__26(v_msg_1144_, v_declHint_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref(v___x_1151_);
v___x_1153_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21_spec__27___redArg(v_ref_1143_, v_a_1152_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1154_, lean_object* v_msg_1155_, lean_object* v_declHint_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1154_, v_msg_1155_, v_declHint_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec_ref(v___y_1157_);
lean_dec(v_ref_1154_);
return v_res_1162_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1164_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__0));
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(lean_object* v_ref_1166_, lean_object* v_constName_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_){
_start:
{
lean_object* v___x_1173_; uint8_t v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1173_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___closed__1);
v___x_1174_ = 0;
lean_inc(v_constName_1167_);
v___x_1175_ = l_Lean_MessageData_ofConstName(v_constName_1167_, v___x_1174_);
v___x_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1173_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__1);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1176_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7_spec__21___redArg(v_ref_1166_, v___x_1178_, v_constName_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg___boxed(lean_object* v_ref_1180_, lean_object* v_constName_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1180_, v_constName_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v_ref_1180_);
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(lean_object* v_constName_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_ref_1194_; lean_object* v___x_1195_; 
v_ref_1194_ = lean_ctor_get(v___y_1191_, 5);
v___x_1195_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2_spec__7___redArg(v_ref_1194_, v_constName_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg___boxed(lean_object* v_constName_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(lean_object* v_constName_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; lean_object* v_env_1210_; uint8_t v___x_1211_; lean_object* v___x_1212_; 
v___x_1209_ = lean_st_ref_get(v___y_1207_);
v_env_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc_ref(v_env_1210_);
lean_dec(v___x_1209_);
v___x_1211_ = 0;
lean_inc(v_constName_1203_);
v___x_1212_ = l_Lean_Environment_find_x3f(v_env_1210_, v_constName_1203_, v___x_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1213_; 
v___x_1213_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2_spec__2___redArg(v_constName_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
return v___x_1213_;
}
else
{
lean_object* v_val_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_constName_1203_);
v_val_1214_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1212_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_val_1214_);
lean_dec(v___x_1212_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set_tag(v___x_1216_, 0);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_val_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2___boxed(lean_object* v_constName_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_constName_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(uint8_t v___x_1229_, lean_object* v_x_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
if (lean_obj_tag(v_x_1230_) == 0)
{
uint8_t v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = 1;
v___x_1237_ = lean_box(v___x_1236_);
v___x_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v_head_1239_; lean_object* v_tail_1240_; lean_object* v___x_1241_; 
v_head_1239_ = lean_ctor_get(v_x_1230_, 0);
lean_inc(v_head_1239_);
v_tail_1240_ = lean_ctor_get(v_x_1230_, 1);
lean_inc(v_tail_1240_);
lean_dec_ref_known(v_x_1230_, 2);
v___x_1241_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_head_1239_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_);
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1262_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1244_ = v___x_1241_;
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1262_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___y_1247_; uint8_t v_a_1248_; 
if (lean_obj_tag(v_a_1242_) == 6)
{
lean_object* v_val_1250_; lean_object* v_numFields_1251_; lean_object* v___x_1252_; uint8_t v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v_val_1250_ = lean_ctor_get(v_a_1242_, 0);
lean_inc_ref(v_val_1250_);
lean_dec_ref_known(v_a_1242_, 1);
v_numFields_1251_ = lean_ctor_get(v_val_1250_, 4);
lean_inc(v_numFields_1251_);
lean_dec_ref(v_val_1250_);
v___x_1252_ = lean_unsigned_to_nat(0u);
v___x_1253_ = lean_nat_dec_eq(v_numFields_1251_, v___x_1252_);
lean_dec(v_numFields_1251_);
v___x_1254_ = lean_box(v___x_1253_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1254_);
v___x_1256_ = v___x_1244_;
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
v___y_1247_ = v___x_1256_;
v_a_1248_ = v___x_1253_;
goto v___jp_1246_;
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
lean_dec(v_a_1242_);
v___x_1258_ = lean_box(v___x_1229_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 0, v___x_1258_);
v___x_1260_ = v___x_1244_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
v___y_1247_ = v___x_1260_;
v_a_1248_ = v___x_1229_;
goto v___jp_1246_;
}
}
v___jp_1246_:
{
if (v_a_1248_ == 0)
{
lean_dec(v_tail_1240_);
return v___y_1247_;
}
else
{
lean_dec_ref(v___y_1247_);
v_x_1230_ = v_tail_1240_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v_tail_1240_);
v_a_1263_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1241_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1241_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13___boxed(lean_object* v___x_1271_, lean_object* v_x_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_){
_start:
{
uint8_t v___x_35691__boxed_1278_; lean_object* v_res_1279_; 
v___x_35691__boxed_1278_ = lean_unbox(v___x_1271_);
v_res_1279_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(v___x_35691__boxed_1278_, v_x_1272_, v___y_1273_, v___y_1274_, v___y_1275_, v___y_1276_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
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
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1342_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1342_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1342_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
if (lean_obj_tag(v_a_1287_) == 5)
{
lean_object* v_val_1291_; lean_object* v_toConstantVal_1292_; lean_object* v_numParams_1293_; lean_object* v_numIndices_1294_; lean_object* v_ctors_1295_; uint8_t v_isRec_1296_; uint8_t v_isUnsafe_1297_; lean_object* v_type_1298_; uint8_t v___x_1299_; 
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
v_type_1298_ = lean_ctor_get(v_toConstantVal_1292_, 2);
v___x_1299_ = l_Lean_Expr_isProp(v_type_1298_);
if (v___x_1299_ == 0)
{
lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1300_ = l_Lean_InductiveVal_numTypeFormers(v_val_1291_);
lean_dec_ref(v_val_1291_);
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_dec_eq(v___x_1300_, v___x_1301_);
lean_dec(v___x_1300_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_dec(v_ctors_1295_);
lean_dec(v_numIndices_1294_);
lean_dec(v_numParams_1293_);
v___x_1303_ = lean_box(v___x_1302_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1303_);
v___x_1305_ = v___x_1289_;
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
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_nat_dec_eq(v_numIndices_1294_, v___x_1307_);
lean_dec(v_numIndices_1294_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
lean_dec(v_ctors_1295_);
lean_dec(v_numParams_1293_);
v___x_1309_ = lean_box(v___x_1308_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1309_);
v___x_1311_ = v___x_1289_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
else
{
uint8_t v___x_1313_; 
v___x_1313_ = lean_nat_dec_eq(v_numParams_1293_, v___x_1307_);
lean_dec(v_numParams_1293_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
lean_dec(v_ctors_1295_);
v___x_1314_ = lean_box(v___x_1313_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1314_);
v___x_1316_ = v___x_1289_;
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
else
{
uint8_t v___x_1318_; 
v___x_1318_ = l_List_isEmpty___redArg(v_ctors_1295_);
if (v___x_1318_ == 0)
{
if (v_isRec_1296_ == 0)
{
if (v_isUnsafe_1297_ == 0)
{
lean_object* v___x_1319_; 
lean_del_object(v___x_1289_);
v___x_1319_ = l_List_allM___at___00Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9_spec__13(v_isUnsafe_1297_, v_ctors_1295_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec(v_ctors_1295_);
v___x_1320_ = lean_box(v_isRec_1296_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1320_);
v___x_1322_ = v___x_1289_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
else
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
lean_dec(v_ctors_1295_);
v___x_1324_ = lean_box(v___x_1318_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1324_);
v___x_1326_ = v___x_1289_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
lean_dec(v_ctors_1295_);
v___x_1328_ = lean_box(v___x_1299_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1328_);
v___x_1330_ = v___x_1289_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
else
{
uint8_t v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
lean_dec(v_ctors_1295_);
lean_dec(v_numIndices_1294_);
lean_dec(v_numParams_1293_);
lean_dec_ref(v_val_1291_);
v___x_1332_ = 0;
v___x_1333_ = lean_box(v___x_1332_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1333_);
v___x_1335_ = v___x_1289_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v_a_1287_);
v___x_1337_ = 0;
v___x_1338_ = lean_box(v___x_1337_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1338_);
v___x_1340_ = v___x_1289_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1286_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1286_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9___boxed(lean_object* v_declName_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(v_declName_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(lean_object* v_env_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; lean_object* v_nextMacroScope_1363_; lean_object* v_ngen_1364_; lean_object* v_auxDeclNGen_1365_; lean_object* v_traceState_1366_; lean_object* v_messages_1367_; lean_object* v_infoState_1368_; lean_object* v_snapshotTasks_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1395_; 
v___x_1362_ = lean_st_ref_take(v___y_1360_);
v_nextMacroScope_1363_ = lean_ctor_get(v___x_1362_, 1);
v_ngen_1364_ = lean_ctor_get(v___x_1362_, 2);
v_auxDeclNGen_1365_ = lean_ctor_get(v___x_1362_, 3);
v_traceState_1366_ = lean_ctor_get(v___x_1362_, 4);
v_messages_1367_ = lean_ctor_get(v___x_1362_, 6);
v_infoState_1368_ = lean_ctor_get(v___x_1362_, 7);
v_snapshotTasks_1369_ = lean_ctor_get(v___x_1362_, 8);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1395_ == 0)
{
lean_object* v_unused_1396_; lean_object* v_unused_1397_; 
v_unused_1396_ = lean_ctor_get(v___x_1362_, 5);
lean_dec(v_unused_1396_);
v_unused_1397_ = lean_ctor_get(v___x_1362_, 0);
lean_dec(v_unused_1397_);
v___x_1371_ = v___x_1362_;
v_isShared_1372_ = v_isSharedCheck_1395_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_snapshotTasks_1369_);
lean_inc(v_infoState_1368_);
lean_inc(v_messages_1367_);
lean_inc(v_traceState_1366_);
lean_inc(v_auxDeclNGen_1365_);
lean_inc(v_ngen_1364_);
lean_inc(v_nextMacroScope_1363_);
lean_dec(v___x_1362_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1395_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 5, v___x_1373_);
lean_ctor_set(v___x_1371_, 0, v_env_1358_);
v___x_1375_ = v___x_1371_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_env_1358_);
lean_ctor_set(v_reuseFailAlloc_1394_, 1, v_nextMacroScope_1363_);
lean_ctor_set(v_reuseFailAlloc_1394_, 2, v_ngen_1364_);
lean_ctor_set(v_reuseFailAlloc_1394_, 3, v_auxDeclNGen_1365_);
lean_ctor_set(v_reuseFailAlloc_1394_, 4, v_traceState_1366_);
lean_ctor_set(v_reuseFailAlloc_1394_, 5, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1394_, 6, v_messages_1367_);
lean_ctor_set(v_reuseFailAlloc_1394_, 7, v_infoState_1368_);
lean_ctor_set(v_reuseFailAlloc_1394_, 8, v_snapshotTasks_1369_);
v___x_1375_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v_mctx_1378_; lean_object* v_zetaDeltaFVarIds_1379_; lean_object* v_postponed_1380_; lean_object* v_diag_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1392_; 
v___x_1376_ = lean_st_ref_set(v___y_1360_, v___x_1375_);
v___x_1377_ = lean_st_ref_take(v___y_1359_);
v_mctx_1378_ = lean_ctor_get(v___x_1377_, 0);
v_zetaDeltaFVarIds_1379_ = lean_ctor_get(v___x_1377_, 2);
v_postponed_1380_ = lean_ctor_get(v___x_1377_, 3);
v_diag_1381_ = lean_ctor_get(v___x_1377_, 4);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v___x_1377_, 1);
lean_dec(v_unused_1393_);
v___x_1383_ = v___x_1377_;
v_isShared_1384_ = v_isSharedCheck_1392_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_diag_1381_);
lean_inc(v_postponed_1380_);
lean_inc(v_zetaDeltaFVarIds_1379_);
lean_inc(v_mctx_1378_);
lean_dec(v___x_1377_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1392_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1385_; lean_object* v___x_1387_; 
v___x_1385_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1385_);
v___x_1387_ = v___x_1383_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_mctx_1378_);
lean_ctor_set(v_reuseFailAlloc_1391_, 1, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1391_, 2, v_zetaDeltaFVarIds_1379_);
lean_ctor_set(v_reuseFailAlloc_1391_, 3, v_postponed_1380_);
lean_ctor_set(v_reuseFailAlloc_1391_, 4, v_diag_1381_);
v___x_1387_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_st_ref_set(v___y_1359_, v___x_1387_);
v___x_1389_ = lean_box(0);
v___x_1390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg___boxed(lean_object* v_env_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(v_env_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec(v___y_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(lean_object* v_declName_1403_, lean_object* v_entry_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
lean_object* v___x_1410_; lean_object* v_env_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1410_ = lean_st_ref_get(v___y_1408_);
v_env_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc_ref(v_env_1411_);
lean_dec(v___x_1410_);
v___x_1412_ = l_Lean_Linter_deprecatedAttr;
v___x_1413_ = l_Lean_ParametricAttribute_setParam___redArg(v___x_1412_, v_env_1411_, v_declName_1403_, v_entry_1404_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1423_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1423_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set_tag(v___x_1416_, 3);
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = l_Lean_MessageData_ofFormat(v___x_1419_);
v___x_1421_ = l_Lean_throwError___at___00Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4_spec__5___redArg(v___x_1420_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1421_;
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1425_; 
v_a_1424_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1425_ = l_Lean_setEnv___at___00Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11_spec__17___redArg(v_a_1424_, v___y_1406_, v___y_1408_);
return v___x_1425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11___boxed(lean_object* v_declName_1426_, lean_object* v_entry_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(v_declName_1426_, v_entry_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1(lean_object* v___x_1440_, lean_object* v___x_1441_, lean_object* v_xs_1442_, uint8_t v___x_1443_, uint8_t v___x_1444_, lean_object* v_val_1445_, lean_object* v___x_1446_, lean_object* v___x_1447_, lean_object* v___x_1448_, lean_object* v___x_1449_, lean_object* v_ctors_1450_, lean_object* v___x_1451_, lean_object* v___x_1452_, lean_object* v_levelParams_1453_, lean_object* v_indName_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___x_1551_; 
lean_inc_ref(v___x_1441_);
lean_inc_ref(v___x_1440_);
v___x_1551_ = l_Lean_mkArrow(v___x_1440_, v___x_1441_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; uint8_t v___x_1553_; lean_object* v___x_1554_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref_known(v___x_1551_, 1);
v___x_1553_ = 1;
v___x_1554_ = l_Lean_Meta_mkForallFVars(v_xs_1442_, v_a_1552_, v___x_1443_, v___x_1444_, v___x_1444_, v___x_1553_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_object* v_a_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___f_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref_known(v___x_1554_, 1);
v___x_1556_ = lean_box(v___x_1443_);
v___x_1557_ = lean_box(v___x_1444_);
v___x_1558_ = lean_box(v___x_1553_);
lean_inc(v___x_1447_);
lean_inc_ref(v_val_1445_);
v___f_1559_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__0___boxed), 18, 12);
lean_closure_set(v___f_1559_, 0, v_xs_1442_);
lean_closure_set(v___f_1559_, 1, v___x_1556_);
lean_closure_set(v___f_1559_, 2, v___x_1557_);
lean_closure_set(v___f_1559_, 3, v___x_1558_);
lean_closure_set(v___f_1559_, 4, v_val_1445_);
lean_closure_set(v___f_1559_, 5, v___x_1446_);
lean_closure_set(v___f_1559_, 6, v___x_1441_);
lean_closure_set(v___f_1559_, 7, v___x_1447_);
lean_closure_set(v___f_1559_, 8, v___x_1448_);
lean_closure_set(v___f_1559_, 9, v___x_1449_);
lean_closure_set(v___f_1559_, 10, v_ctors_1450_);
lean_closure_set(v___f_1559_, 11, v___x_1451_);
v___x_1560_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__3));
v___x_1561_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCtorIdx_spec__7___redArg(v___x_1560_, v___x_1440_, v___f_1559_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1563_; lean_object* v_env_1564_; uint32_t v___x_1565_; uint32_t v___x_1566_; uint32_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1771_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc_n(v_a_1562_, 2);
lean_dec_ref_known(v___x_1561_, 1);
v___x_1563_ = lean_st_ref_get(v___y_1458_);
v_env_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_env_1564_);
lean_dec(v___x_1563_);
v___x_1565_ = l_Lean_getMaxHeight(v_env_1564_, v_a_1562_);
v___x_1566_ = 1;
v___x_1567_ = lean_uint32_add(v___x_1565_, v___x_1566_);
v___x_1568_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_1568_, 0, v___x_1567_);
lean_inc(v_a_1555_);
lean_inc(v_levelParams_1453_);
lean_inc(v___x_1452_);
v___x_1569_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1452_, v_levelParams_1453_, v_a_1555_, v_a_1562_, v___x_1568_, v___y_1458_);
v_a_1570_ = lean_ctor_get(v___x_1569_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1569_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1572_ = v___x_1569_;
v_isShared_1573_ = v_isSharedCheck_1771_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1569_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1771_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 1);
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; lean_object* v___y_1580_; lean_object* v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v___y_1657_; lean_object* v___x_1696_; 
lean_inc_ref(v___x_1575_);
v___x_1696_ = l_Lean_addDecl(v___x_1575_, v___x_1443_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v___x_1697_; lean_object* v_env_1698_; lean_object* v_nextMacroScope_1699_; lean_object* v_ngen_1700_; lean_object* v_auxDeclNGen_1701_; lean_object* v_traceState_1702_; lean_object* v_messages_1703_; lean_object* v_infoState_1704_; lean_object* v_snapshotTasks_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1768_; 
lean_dec_ref_known(v___x_1696_, 1);
v___x_1697_ = lean_st_ref_take(v___y_1458_);
v_env_1698_ = lean_ctor_get(v___x_1697_, 0);
v_nextMacroScope_1699_ = lean_ctor_get(v___x_1697_, 1);
v_ngen_1700_ = lean_ctor_get(v___x_1697_, 2);
v_auxDeclNGen_1701_ = lean_ctor_get(v___x_1697_, 3);
v_traceState_1702_ = lean_ctor_get(v___x_1697_, 4);
v_messages_1703_ = lean_ctor_get(v___x_1697_, 6);
v_infoState_1704_ = lean_ctor_get(v___x_1697_, 7);
v_snapshotTasks_1705_ = lean_ctor_get(v___x_1697_, 8);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1768_ == 0)
{
lean_object* v_unused_1769_; 
v_unused_1769_ = lean_ctor_get(v___x_1697_, 5);
lean_dec(v_unused_1769_);
v___x_1707_ = v___x_1697_;
v_isShared_1708_ = v_isSharedCheck_1768_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_snapshotTasks_1705_);
lean_inc(v_infoState_1704_);
lean_inc(v_messages_1703_);
lean_inc(v_traceState_1702_);
lean_inc(v_auxDeclNGen_1701_);
lean_inc(v_ngen_1700_);
lean_inc(v_nextMacroScope_1699_);
lean_inc(v_env_1698_);
lean_dec(v___x_1697_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1768_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_inc(v___x_1452_);
v___x_1709_ = l_Lean_Meta_addToCompletionBlackList(v_env_1698_, v___x_1452_);
v___x_1710_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 5, v___x_1710_);
lean_ctor_set(v___x_1707_, 0, v___x_1709_);
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v___x_1709_);
lean_ctor_set(v_reuseFailAlloc_1767_, 1, v_nextMacroScope_1699_);
lean_ctor_set(v_reuseFailAlloc_1767_, 2, v_ngen_1700_);
lean_ctor_set(v_reuseFailAlloc_1767_, 3, v_auxDeclNGen_1701_);
lean_ctor_set(v_reuseFailAlloc_1767_, 4, v_traceState_1702_);
lean_ctor_set(v_reuseFailAlloc_1767_, 5, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1767_, 6, v_messages_1703_);
lean_ctor_set(v_reuseFailAlloc_1767_, 7, v_infoState_1704_);
lean_ctor_set(v_reuseFailAlloc_1767_, 8, v_snapshotTasks_1705_);
v___x_1712_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v_mctx_1715_; lean_object* v_zetaDeltaFVarIds_1716_; lean_object* v_postponed_1717_; lean_object* v_diag_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1765_; 
v___x_1713_ = lean_st_ref_set(v___y_1458_, v___x_1712_);
v___x_1714_ = lean_st_ref_take(v___y_1456_);
v_mctx_1715_ = lean_ctor_get(v___x_1714_, 0);
v_zetaDeltaFVarIds_1716_ = lean_ctor_get(v___x_1714_, 2);
v_postponed_1717_ = lean_ctor_get(v___x_1714_, 3);
v_diag_1718_ = lean_ctor_get(v___x_1714_, 4);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1714_, 1);
lean_dec(v_unused_1766_);
v___x_1720_ = v___x_1714_;
v_isShared_1721_ = v_isSharedCheck_1765_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_diag_1718_);
lean_inc(v_postponed_1717_);
lean_inc(v_zetaDeltaFVarIds_1716_);
lean_inc(v_mctx_1715_);
lean_dec(v___x_1714_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1765_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_mctx_1715_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1764_, 2, v_zetaDeltaFVarIds_1716_);
lean_ctor_set(v_reuseFailAlloc_1764_, 3, v_postponed_1717_);
lean_ctor_set(v_reuseFailAlloc_1764_, 4, v_diag_1718_);
v___x_1724_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v_env_1727_; lean_object* v_nextMacroScope_1728_; lean_object* v_ngen_1729_; lean_object* v_auxDeclNGen_1730_; lean_object* v_traceState_1731_; lean_object* v_messages_1732_; lean_object* v_infoState_1733_; lean_object* v_snapshotTasks_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1762_; 
v___x_1725_ = lean_st_ref_set(v___y_1456_, v___x_1724_);
v___x_1726_ = lean_st_ref_take(v___y_1458_);
v_env_1727_ = lean_ctor_get(v___x_1726_, 0);
v_nextMacroScope_1728_ = lean_ctor_get(v___x_1726_, 1);
v_ngen_1729_ = lean_ctor_get(v___x_1726_, 2);
v_auxDeclNGen_1730_ = lean_ctor_get(v___x_1726_, 3);
v_traceState_1731_ = lean_ctor_get(v___x_1726_, 4);
v_messages_1732_ = lean_ctor_get(v___x_1726_, 6);
v_infoState_1733_ = lean_ctor_get(v___x_1726_, 7);
v_snapshotTasks_1734_ = lean_ctor_get(v___x_1726_, 8);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1762_ == 0)
{
lean_object* v_unused_1763_; 
v_unused_1763_ = lean_ctor_get(v___x_1726_, 5);
lean_dec(v_unused_1763_);
v___x_1736_ = v___x_1726_;
v_isShared_1737_ = v_isSharedCheck_1762_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_snapshotTasks_1734_);
lean_inc(v_infoState_1733_);
lean_inc(v_messages_1732_);
lean_inc(v_traceState_1731_);
lean_inc(v_auxDeclNGen_1730_);
lean_inc(v_ngen_1729_);
lean_inc(v_nextMacroScope_1728_);
lean_inc(v_env_1727_);
lean_dec(v___x_1726_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1762_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
lean_inc(v___x_1452_);
v___x_1738_ = l_Lean_addProtected(v_env_1727_, v___x_1452_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 5, v___x_1710_);
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_nextMacroScope_1728_);
lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_ngen_1729_);
lean_ctor_set(v_reuseFailAlloc_1761_, 3, v_auxDeclNGen_1730_);
lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_traceState_1731_);
lean_ctor_set(v_reuseFailAlloc_1761_, 5, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1761_, 6, v_messages_1732_);
lean_ctor_set(v_reuseFailAlloc_1761_, 7, v_infoState_1733_);
lean_ctor_set(v_reuseFailAlloc_1761_, 8, v_snapshotTasks_1734_);
v___x_1740_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v_mctx_1743_; lean_object* v_zetaDeltaFVarIds_1744_; lean_object* v_postponed_1745_; lean_object* v_diag_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1759_; 
v___x_1741_ = lean_st_ref_set(v___y_1458_, v___x_1740_);
v___x_1742_ = lean_st_ref_take(v___y_1456_);
v_mctx_1743_ = lean_ctor_get(v___x_1742_, 0);
v_zetaDeltaFVarIds_1744_ = lean_ctor_get(v___x_1742_, 2);
v_postponed_1745_ = lean_ctor_get(v___x_1742_, 3);
v_diag_1746_ = lean_ctor_get(v___x_1742_, 4);
v_isSharedCheck_1759_ = !lean_is_exclusive(v___x_1742_);
if (v_isSharedCheck_1759_ == 0)
{
lean_object* v_unused_1760_; 
v_unused_1760_ = lean_ctor_get(v___x_1742_, 1);
lean_dec(v_unused_1760_);
v___x_1748_ = v___x_1742_;
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_diag_1746_);
lean_inc(v_postponed_1745_);
lean_inc(v_zetaDeltaFVarIds_1744_);
lean_inc(v_mctx_1743_);
lean_dec(v___x_1742_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1759_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set(v___x_1748_, 1, v___x_1722_);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v_mctx_1743_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_zetaDeltaFVarIds_1744_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_postponed_1745_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_diag_1746_);
v___x_1751_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1752_ = lean_st_ref_set(v___y_1456_, v___x_1751_);
v___x_1753_ = lean_unsigned_to_nat(1u);
v___x_1754_ = l_Lean_InductiveVal_numCtors(v_val_1445_);
lean_dec_ref(v_val_1445_);
v___x_1755_ = lean_nat_dec_eq(v___x_1754_, v___x_1753_);
lean_dec(v___x_1754_);
if (v___x_1755_ == 0)
{
v___y_1654_ = v___y_1455_;
v___y_1655_ = v___y_1456_;
v___y_1656_ = v___y_1457_;
v___y_1657_ = v___y_1458_;
goto v___jp_1653_;
}
else
{
uint8_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1756_ = 2;
lean_inc(v___x_1452_);
v___x_1757_ = l_Lean_Meta_setInlineAttribute(v___x_1452_, v___x_1756_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_dec_ref_known(v___x_1757_, 1);
v___y_1654_ = v___y_1455_;
v___y_1655_ = v___y_1456_;
v___y_1656_ = v___y_1457_;
v___y_1657_ = v___y_1458_;
goto v___jp_1653_;
}
else
{
lean_dec_ref(v___x_1575_);
lean_dec(v_a_1555_);
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1447_);
return v___x_1757_;
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
lean_dec_ref(v___x_1575_);
lean_dec(v_a_1555_);
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1447_);
lean_dec_ref(v_val_1445_);
return v___x_1696_;
}
v___jp_1576_:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_compileDecl(v___x_1575_, v___x_1444_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1581_) == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref_known(v___x_1581_, 1);
lean_inc(v___x_1452_);
v___x_1582_ = l_Lean_enableRealizationsForConst(v___x_1452_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v___x_1583_; 
lean_dec_ref_known(v___x_1582_, 1);
lean_inc(v_indName_1454_);
v___x_1583_ = l_Lean_isEnumType___at___00Lean_mkCtorIdx_spec__9(v_indName_1454_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1644_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1644_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1644_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
uint8_t v___x_1588_; 
v___x_1588_ = lean_unbox(v_a_1584_);
lean_dec(v_a_1584_);
if (v___x_1588_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_dec(v_a_1555_);
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1447_);
v___x_1589_ = lean_box(0);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_a_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1643_; 
lean_del_object(v___x_1586_);
lean_inc(v_indName_1454_);
v___x_1593_ = l_Lean_mkToCtorIdxName(v_indName_1454_);
lean_inc(v___x_1452_);
v___x_1594_ = l_Lean_mkConst(v___x_1452_, v___x_1447_);
v___x_1595_ = lean_box(1);
lean_inc(v___x_1593_);
v___x_1596_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCtorIdx_spec__8___redArg(v___x_1593_, v_levelParams_1453_, v_a_1555_, v___x_1594_, v___x_1595_, v___y_1580_);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1599_ = v___x_1596_;
v_isShared_1600_ = v_isSharedCheck_1643_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_a_1597_);
lean_dec(v___x_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1643_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1602_; 
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 1);
v___x_1602_ = v___x_1599_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1597_);
v___x_1602_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Lean_addDecl(v___x_1602_, v___x_1443_, v___y_1579_, v___y_1580_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v___x_1604_; lean_object* v_env_1605_; uint8_t v___x_1606_; 
lean_dec_ref_known(v___x_1603_, 1);
v___x_1604_ = lean_st_ref_get(v___y_1580_);
v_env_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc_ref(v_env_1605_);
lean_dec(v___x_1604_);
v___x_1606_ = l_Lean_isMarkedMeta(v_env_1605_, v_indName_1454_);
if (v___x_1606_ == 0)
{
v___y_1461_ = v___x_1593_;
v___y_1462_ = v___y_1577_;
v___y_1463_ = v___y_1578_;
v___y_1464_ = v___y_1579_;
v___y_1465_ = v___y_1580_;
goto v___jp_1460_;
}
else
{
lean_object* v___x_1607_; lean_object* v_env_1608_; lean_object* v_nextMacroScope_1609_; lean_object* v_ngen_1610_; lean_object* v_auxDeclNGen_1611_; lean_object* v_traceState_1612_; lean_object* v_messages_1613_; lean_object* v_infoState_1614_; lean_object* v_snapshotTasks_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1640_; 
v___x_1607_ = lean_st_ref_take(v___y_1580_);
v_env_1608_ = lean_ctor_get(v___x_1607_, 0);
v_nextMacroScope_1609_ = lean_ctor_get(v___x_1607_, 1);
v_ngen_1610_ = lean_ctor_get(v___x_1607_, 2);
v_auxDeclNGen_1611_ = lean_ctor_get(v___x_1607_, 3);
v_traceState_1612_ = lean_ctor_get(v___x_1607_, 4);
v_messages_1613_ = lean_ctor_get(v___x_1607_, 6);
v_infoState_1614_ = lean_ctor_get(v___x_1607_, 7);
v_snapshotTasks_1615_ = lean_ctor_get(v___x_1607_, 8);
v_isSharedCheck_1640_ = !lean_is_exclusive(v___x_1607_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; 
v_unused_1641_ = lean_ctor_get(v___x_1607_, 5);
lean_dec(v_unused_1641_);
v___x_1617_ = v___x_1607_;
v_isShared_1618_ = v_isSharedCheck_1640_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_snapshotTasks_1615_);
lean_inc(v_infoState_1614_);
lean_inc(v_messages_1613_);
lean_inc(v_traceState_1612_);
lean_inc(v_auxDeclNGen_1611_);
lean_inc(v_ngen_1610_);
lean_inc(v_nextMacroScope_1609_);
lean_inc(v_env_1608_);
lean_dec(v___x_1607_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1640_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
lean_inc(v___x_1593_);
v___x_1619_ = l_Lean_markMeta(v_env_1608_, v___x_1593_);
v___x_1620_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 5, v___x_1620_);
lean_ctor_set(v___x_1617_, 0, v___x_1619_);
v___x_1622_ = v___x_1617_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_nextMacroScope_1609_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v_ngen_1610_);
lean_ctor_set(v_reuseFailAlloc_1639_, 3, v_auxDeclNGen_1611_);
lean_ctor_set(v_reuseFailAlloc_1639_, 4, v_traceState_1612_);
lean_ctor_set(v_reuseFailAlloc_1639_, 5, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1639_, 6, v_messages_1613_);
lean_ctor_set(v_reuseFailAlloc_1639_, 7, v_infoState_1614_);
lean_ctor_set(v_reuseFailAlloc_1639_, 8, v_snapshotTasks_1615_);
v___x_1622_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v_mctx_1625_; lean_object* v_zetaDeltaFVarIds_1626_; lean_object* v_postponed_1627_; lean_object* v_diag_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1637_; 
v___x_1623_ = lean_st_ref_set(v___y_1580_, v___x_1622_);
v___x_1624_ = lean_st_ref_take(v___y_1578_);
v_mctx_1625_ = lean_ctor_get(v___x_1624_, 0);
v_zetaDeltaFVarIds_1626_ = lean_ctor_get(v___x_1624_, 2);
v_postponed_1627_ = lean_ctor_get(v___x_1624_, 3);
v_diag_1628_ = lean_ctor_get(v___x_1624_, 4);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1637_ == 0)
{
lean_object* v_unused_1638_; 
v_unused_1638_ = lean_ctor_get(v___x_1624_, 1);
lean_dec(v_unused_1638_);
v___x_1630_ = v___x_1624_;
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_diag_1628_);
lean_inc(v_postponed_1627_);
lean_inc(v_zetaDeltaFVarIds_1626_);
lean_inc(v_mctx_1625_);
lean_dec(v___x_1624_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1637_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1632_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 1, v___x_1632_);
v___x_1634_ = v___x_1630_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_mctx_1625_);
lean_ctor_set(v_reuseFailAlloc_1636_, 1, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1636_, 2, v_zetaDeltaFVarIds_1626_);
lean_ctor_set(v_reuseFailAlloc_1636_, 3, v_postponed_1627_);
lean_ctor_set(v_reuseFailAlloc_1636_, 4, v_diag_1628_);
v___x_1634_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
lean_object* v___x_1635_; 
v___x_1635_ = lean_st_ref_set(v___y_1578_, v___x_1634_);
v___y_1461_ = v___x_1593_;
v___y_1462_ = v___y_1577_;
v___y_1463_ = v___y_1578_;
v___y_1464_ = v___y_1579_;
v___y_1465_ = v___y_1580_;
goto v___jp_1460_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1593_);
lean_dec(v_indName_1454_);
lean_dec(v___x_1452_);
return v___x_1603_;
}
}
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_dec(v_a_1555_);
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1447_);
v_a_1645_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1583_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1583_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
else
{
lean_dec(v_a_1555_);
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1447_);
return v___x_1582_;
}
}
else
{
lean_dec(v_a_1555_);
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1447_);
return v___x_1581_;
}
}
v___jp_1653_:
{
lean_object* v___x_1658_; lean_object* v_env_1659_; uint8_t v___x_1660_; 
v___x_1658_ = lean_st_ref_get(v___y_1657_);
v_env_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc_ref(v_env_1659_);
lean_dec(v___x_1658_);
lean_inc(v_indName_1454_);
v___x_1660_ = l_Lean_isMarkedMeta(v_env_1659_, v_indName_1454_);
if (v___x_1660_ == 0)
{
v___y_1577_ = v___y_1654_;
v___y_1578_ = v___y_1655_;
v___y_1579_ = v___y_1656_;
v___y_1580_ = v___y_1657_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1661_; lean_object* v_env_1662_; lean_object* v_nextMacroScope_1663_; lean_object* v_ngen_1664_; lean_object* v_auxDeclNGen_1665_; lean_object* v_traceState_1666_; lean_object* v_messages_1667_; lean_object* v_infoState_1668_; lean_object* v_snapshotTasks_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1694_; 
v___x_1661_ = lean_st_ref_take(v___y_1657_);
v_env_1662_ = lean_ctor_get(v___x_1661_, 0);
v_nextMacroScope_1663_ = lean_ctor_get(v___x_1661_, 1);
v_ngen_1664_ = lean_ctor_get(v___x_1661_, 2);
v_auxDeclNGen_1665_ = lean_ctor_get(v___x_1661_, 3);
v_traceState_1666_ = lean_ctor_get(v___x_1661_, 4);
v_messages_1667_ = lean_ctor_get(v___x_1661_, 6);
v_infoState_1668_ = lean_ctor_get(v___x_1661_, 7);
v_snapshotTasks_1669_ = lean_ctor_get(v___x_1661_, 8);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1661_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v___x_1661_, 5);
lean_dec(v_unused_1695_);
v___x_1671_ = v___x_1661_;
v_isShared_1672_ = v_isSharedCheck_1694_;
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
v_isShared_1672_ = v_isSharedCheck_1694_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1676_; 
lean_inc(v___x_1452_);
v___x_1673_ = l_Lean_markMeta(v_env_1662_, v___x_1452_);
v___x_1674_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 5, v___x_1674_);
lean_ctor_set(v___x_1671_, 0, v___x_1673_);
v___x_1676_ = v___x_1671_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1673_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_nextMacroScope_1663_);
lean_ctor_set(v_reuseFailAlloc_1693_, 2, v_ngen_1664_);
lean_ctor_set(v_reuseFailAlloc_1693_, 3, v_auxDeclNGen_1665_);
lean_ctor_set(v_reuseFailAlloc_1693_, 4, v_traceState_1666_);
lean_ctor_set(v_reuseFailAlloc_1693_, 5, v___x_1674_);
lean_ctor_set(v_reuseFailAlloc_1693_, 6, v_messages_1667_);
lean_ctor_set(v_reuseFailAlloc_1693_, 7, v_infoState_1668_);
lean_ctor_set(v_reuseFailAlloc_1693_, 8, v_snapshotTasks_1669_);
v___x_1676_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_mctx_1679_; lean_object* v_zetaDeltaFVarIds_1680_; lean_object* v_postponed_1681_; lean_object* v_diag_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1691_; 
v___x_1677_ = lean_st_ref_set(v___y_1657_, v___x_1676_);
v___x_1678_ = lean_st_ref_take(v___y_1655_);
v_mctx_1679_ = lean_ctor_get(v___x_1678_, 0);
v_zetaDeltaFVarIds_1680_ = lean_ctor_get(v___x_1678_, 2);
v_postponed_1681_ = lean_ctor_get(v___x_1678_, 3);
v_diag_1682_ = lean_ctor_get(v___x_1678_, 4);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v___x_1678_, 1);
lean_dec(v_unused_1692_);
v___x_1684_ = v___x_1678_;
v_isShared_1685_ = v_isSharedCheck_1691_;
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
v_isShared_1685_ = v_isSharedCheck_1691_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v___x_1688_; 
v___x_1686_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1686_);
v___x_1688_ = v___x_1684_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_mctx_1679_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1686_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_zetaDeltaFVarIds_1680_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_postponed_1681_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_diag_1682_);
v___x_1688_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_st_ref_set(v___y_1655_, v___x_1688_);
v___y_1577_ = v___y_1654_;
v___y_1578_ = v___y_1655_;
v___y_1579_ = v___y_1656_;
v___y_1580_ = v___y_1657_;
goto v___jp_1576_;
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
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_a_1555_);
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1447_);
lean_dec_ref(v_val_1445_);
v_a_1772_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1561_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1561_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1451_);
lean_dec(v_ctors_1450_);
lean_dec_ref(v___x_1449_);
lean_dec(v___x_1448_);
lean_dec(v___x_1447_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v_val_1445_);
lean_dec_ref(v_xs_1442_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v___x_1440_);
v_a_1780_ = lean_ctor_get(v___x_1554_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1554_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1554_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1554_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec(v_indName_1454_);
lean_dec(v_levelParams_1453_);
lean_dec(v___x_1452_);
lean_dec(v___x_1451_);
lean_dec(v_ctors_1450_);
lean_dec_ref(v___x_1449_);
lean_dec(v___x_1448_);
lean_dec(v___x_1447_);
lean_dec_ref(v___x_1446_);
lean_dec_ref(v_val_1445_);
lean_dec_ref(v_xs_1442_);
lean_dec_ref(v___x_1441_);
lean_dec_ref(v___x_1440_);
v_a_1788_ = lean_ctor_get(v___x_1551_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1551_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1551_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1551_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
v___jp_1460_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1466_ = lean_unsigned_to_nat(1u);
v___x_1467_ = lean_mk_empty_array_with_capacity(v___x_1466_);
lean_inc(v___y_1461_);
v___x_1468_ = lean_array_push(v___x_1467_, v___y_1461_);
v___x_1469_ = l_Lean_compileDecls(v___x_1468_, v___x_1444_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v___x_1470_; lean_object* v_env_1471_; lean_object* v_nextMacroScope_1472_; lean_object* v_ngen_1473_; lean_object* v_auxDeclNGen_1474_; lean_object* v_traceState_1475_; lean_object* v_messages_1476_; lean_object* v_infoState_1477_; lean_object* v_snapshotTasks_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1549_; 
lean_dec_ref_known(v___x_1469_, 1);
v___x_1470_ = lean_st_ref_take(v___y_1465_);
v_env_1471_ = lean_ctor_get(v___x_1470_, 0);
v_nextMacroScope_1472_ = lean_ctor_get(v___x_1470_, 1);
v_ngen_1473_ = lean_ctor_get(v___x_1470_, 2);
v_auxDeclNGen_1474_ = lean_ctor_get(v___x_1470_, 3);
v_traceState_1475_ = lean_ctor_get(v___x_1470_, 4);
v_messages_1476_ = lean_ctor_get(v___x_1470_, 6);
v_infoState_1477_ = lean_ctor_get(v___x_1470_, 7);
v_snapshotTasks_1478_ = lean_ctor_get(v___x_1470_, 8);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1549_ == 0)
{
lean_object* v_unused_1550_; 
v_unused_1550_ = lean_ctor_get(v___x_1470_, 5);
lean_dec(v_unused_1550_);
v___x_1480_ = v___x_1470_;
v_isShared_1481_ = v_isSharedCheck_1549_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_snapshotTasks_1478_);
lean_inc(v_infoState_1477_);
lean_inc(v_messages_1476_);
lean_inc(v_traceState_1475_);
lean_inc(v_auxDeclNGen_1474_);
lean_inc(v_ngen_1473_);
lean_inc(v_nextMacroScope_1472_);
lean_inc(v_env_1471_);
lean_dec(v___x_1470_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1549_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1485_; 
lean_inc(v___y_1461_);
v___x_1482_ = l_Lean_Meta_addToCompletionBlackList(v_env_1471_, v___y_1461_);
v___x_1483_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__2);
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 5, v___x_1483_);
lean_ctor_set(v___x_1480_, 0, v___x_1482_);
v___x_1485_ = v___x_1480_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_nextMacroScope_1472_);
lean_ctor_set(v_reuseFailAlloc_1548_, 2, v_ngen_1473_);
lean_ctor_set(v_reuseFailAlloc_1548_, 3, v_auxDeclNGen_1474_);
lean_ctor_set(v_reuseFailAlloc_1548_, 4, v_traceState_1475_);
lean_ctor_set(v_reuseFailAlloc_1548_, 5, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1548_, 6, v_messages_1476_);
lean_ctor_set(v_reuseFailAlloc_1548_, 7, v_infoState_1477_);
lean_ctor_set(v_reuseFailAlloc_1548_, 8, v_snapshotTasks_1478_);
v___x_1485_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v_mctx_1488_; lean_object* v_zetaDeltaFVarIds_1489_; lean_object* v_postponed_1490_; lean_object* v_diag_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1546_; 
v___x_1486_ = lean_st_ref_set(v___y_1465_, v___x_1485_);
v___x_1487_ = lean_st_ref_take(v___y_1463_);
v_mctx_1488_ = lean_ctor_get(v___x_1487_, 0);
v_zetaDeltaFVarIds_1489_ = lean_ctor_get(v___x_1487_, 2);
v_postponed_1490_ = lean_ctor_get(v___x_1487_, 3);
v_diag_1491_ = lean_ctor_get(v___x_1487_, 4);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1487_);
if (v_isSharedCheck_1546_ == 0)
{
lean_object* v_unused_1547_; 
v_unused_1547_ = lean_ctor_get(v___x_1487_, 1);
lean_dec(v_unused_1547_);
v___x_1493_ = v___x_1487_;
v_isShared_1494_ = v_isSharedCheck_1546_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_diag_1491_);
lean_inc(v_postponed_1490_);
lean_inc(v_zetaDeltaFVarIds_1489_);
lean_inc(v_mctx_1488_);
lean_dec(v___x_1487_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1546_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3, &l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg___closed__3);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_mctx_1488_);
lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_zetaDeltaFVarIds_1489_);
lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_postponed_1490_);
lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_diag_1491_);
v___x_1497_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v_env_1500_; lean_object* v_nextMacroScope_1501_; lean_object* v_ngen_1502_; lean_object* v_auxDeclNGen_1503_; lean_object* v_traceState_1504_; lean_object* v_messages_1505_; lean_object* v_infoState_1506_; lean_object* v_snapshotTasks_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1543_; 
v___x_1498_ = lean_st_ref_set(v___y_1463_, v___x_1497_);
v___x_1499_ = lean_st_ref_take(v___y_1465_);
v_env_1500_ = lean_ctor_get(v___x_1499_, 0);
v_nextMacroScope_1501_ = lean_ctor_get(v___x_1499_, 1);
v_ngen_1502_ = lean_ctor_get(v___x_1499_, 2);
v_auxDeclNGen_1503_ = lean_ctor_get(v___x_1499_, 3);
v_traceState_1504_ = lean_ctor_get(v___x_1499_, 4);
v_messages_1505_ = lean_ctor_get(v___x_1499_, 6);
v_infoState_1506_ = lean_ctor_get(v___x_1499_, 7);
v_snapshotTasks_1507_ = lean_ctor_get(v___x_1499_, 8);
v_isSharedCheck_1543_ = !lean_is_exclusive(v___x_1499_);
if (v_isSharedCheck_1543_ == 0)
{
lean_object* v_unused_1544_; 
v_unused_1544_ = lean_ctor_get(v___x_1499_, 5);
lean_dec(v_unused_1544_);
v___x_1509_ = v___x_1499_;
v_isShared_1510_ = v_isSharedCheck_1543_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_snapshotTasks_1507_);
lean_inc(v_infoState_1506_);
lean_inc(v_messages_1505_);
lean_inc(v_traceState_1504_);
lean_inc(v_auxDeclNGen_1503_);
lean_inc(v_ngen_1502_);
lean_inc(v_nextMacroScope_1501_);
lean_inc(v_env_1500_);
lean_dec(v___x_1499_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1543_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1511_; lean_object* v___x_1513_; 
lean_inc(v___y_1461_);
v___x_1511_ = l_Lean_addProtected(v_env_1500_, v___y_1461_);
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 5, v___x_1483_);
lean_ctor_set(v___x_1509_, 0, v___x_1511_);
v___x_1513_ = v___x_1509_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_nextMacroScope_1501_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_ngen_1502_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_auxDeclNGen_1503_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_traceState_1504_);
lean_ctor_set(v_reuseFailAlloc_1542_, 5, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1542_, 6, v_messages_1505_);
lean_ctor_set(v_reuseFailAlloc_1542_, 7, v_infoState_1506_);
lean_ctor_set(v_reuseFailAlloc_1542_, 8, v_snapshotTasks_1507_);
v___x_1513_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v_mctx_1516_; lean_object* v_zetaDeltaFVarIds_1517_; lean_object* v_postponed_1518_; lean_object* v_diag_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1540_; 
v___x_1514_ = lean_st_ref_set(v___y_1465_, v___x_1513_);
v___x_1515_ = lean_st_ref_take(v___y_1463_);
v_mctx_1516_ = lean_ctor_get(v___x_1515_, 0);
v_zetaDeltaFVarIds_1517_ = lean_ctor_get(v___x_1515_, 2);
v_postponed_1518_ = lean_ctor_get(v___x_1515_, 3);
v_diag_1519_ = lean_ctor_get(v___x_1515_, 4);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1540_ == 0)
{
lean_object* v_unused_1541_; 
v_unused_1541_ = lean_ctor_get(v___x_1515_, 1);
lean_dec(v_unused_1541_);
v___x_1521_ = v___x_1515_;
v_isShared_1522_ = v_isSharedCheck_1540_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_diag_1519_);
lean_inc(v_postponed_1518_);
lean_inc(v_zetaDeltaFVarIds_1517_);
lean_inc(v_mctx_1516_);
lean_dec(v___x_1515_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1540_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1495_);
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_mctx_1516_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_zetaDeltaFVarIds_1517_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_postponed_1518_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_diag_1519_);
v___x_1524_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1537_; 
v___x_1525_ = lean_st_ref_set(v___y_1463_, v___x_1524_);
lean_inc(v___y_1461_);
v___x_1526_ = l_Lean_setReducibleAttribute___at___00Lean_mkCtorIdx_spec__10(v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1537_ == 0)
{
lean_object* v_unused_1538_; 
v_unused_1538_ = lean_ctor_get(v___x_1526_, 0);
lean_dec(v_unused_1538_);
v___x_1528_ = v___x_1526_;
v_isShared_1529_ = v_isSharedCheck_1537_;
goto v_resetjp_1527_;
}
else
{
lean_dec(v___x_1526_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1537_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 1);
lean_ctor_set(v___x_1528_, 0, v___x_1452_);
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1452_);
v___x_1531_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__1___closed__1));
v___x_1534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1531_);
lean_ctor_set(v___x_1534_, 1, v___x_1532_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
v___x_1535_ = l_Lean_Linter_setDeprecated___at___00Lean_mkCtorIdx_spec__11(v___y_1461_, v___x_1534_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1535_;
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
lean_dec(v___y_1461_);
lean_dec(v___x_1452_);
return v___x_1469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__1___boxed(lean_object** _args){
lean_object* v___x_1796_ = _args[0];
lean_object* v___x_1797_ = _args[1];
lean_object* v_xs_1798_ = _args[2];
lean_object* v___x_1799_ = _args[3];
lean_object* v___x_1800_ = _args[4];
lean_object* v_val_1801_ = _args[5];
lean_object* v___x_1802_ = _args[6];
lean_object* v___x_1803_ = _args[7];
lean_object* v___x_1804_ = _args[8];
lean_object* v___x_1805_ = _args[9];
lean_object* v_ctors_1806_ = _args[10];
lean_object* v___x_1807_ = _args[11];
lean_object* v___x_1808_ = _args[12];
lean_object* v_levelParams_1809_ = _args[13];
lean_object* v_indName_1810_ = _args[14];
lean_object* v___y_1811_ = _args[15];
lean_object* v___y_1812_ = _args[16];
lean_object* v___y_1813_ = _args[17];
lean_object* v___y_1814_ = _args[18];
lean_object* v___y_1815_ = _args[19];
_start:
{
uint8_t v___x_36096__boxed_1816_; uint8_t v___x_36097__boxed_1817_; lean_object* v_res_1818_; 
v___x_36096__boxed_1816_ = lean_unbox(v___x_1799_);
v___x_36097__boxed_1817_ = lean_unbox(v___x_1800_);
v_res_1818_ = l_Lean_mkCtorIdx___lam__1(v___x_1796_, v___x_1797_, v_xs_1798_, v___x_36096__boxed_1816_, v___x_36097__boxed_1817_, v_val_1801_, v___x_1802_, v___x_1803_, v___x_1804_, v___x_1805_, v_ctors_1806_, v___x_1807_, v___x_1808_, v_levelParams_1809_, v_indName_1810_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
lean_dec(v___y_1814_);
lean_dec_ref(v___y_1813_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(lean_object* v_bs_1819_, lean_object* v_k_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp(lean_box(0), v_bs_1819_, v_k_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_);
if (lean_obj_tag(v___x_1826_) == 0)
{
lean_object* v_a_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1834_; 
v_a_1827_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1829_ = v___x_1826_;
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_a_1827_);
lean_dec(v___x_1826_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1834_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1830_ == 0)
{
v___x_1832_ = v___x_1829_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_a_1827_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
v_a_1835_ = lean_ctor_get(v___x_1826_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1826_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1826_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg___boxed(lean_object* v_bs_1843_, lean_object* v_k_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(v_bs_1843_, v_k_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v_bs_1843_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(size_t v_sz_1851_, size_t v_i_1852_, lean_object* v_bs_1853_){
_start:
{
uint8_t v___x_1854_; 
v___x_1854_ = lean_usize_dec_lt(v_i_1852_, v_sz_1851_);
if (v___x_1854_ == 0)
{
return v_bs_1853_;
}
else
{
lean_object* v_v_1855_; lean_object* v___x_1856_; lean_object* v_bs_x27_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; lean_object* v___x_1864_; 
v_v_1855_ = lean_array_uget(v_bs_1853_, v_i_1852_);
v___x_1856_ = lean_unsigned_to_nat(0u);
v_bs_x27_1857_ = lean_array_uset(v_bs_1853_, v_i_1852_, v___x_1856_);
v___x_1858_ = l_Lean_Expr_fvarId_x21(v_v_1855_);
lean_dec(v_v_1855_);
v___x_1859_ = 1;
v___x_1860_ = lean_box(v___x_1859_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1858_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = ((size_t)1ULL);
v___x_1863_ = lean_usize_add(v_i_1852_, v___x_1862_);
v___x_1864_ = lean_array_uset(v_bs_x27_1857_, v_i_1852_, v___x_1861_);
v_i_1852_ = v___x_1863_;
v_bs_1853_ = v___x_1864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19___boxed(lean_object* v_sz_1866_, lean_object* v_i_1867_, lean_object* v_bs_1868_){
_start:
{
size_t v_sz_boxed_1869_; size_t v_i_boxed_1870_; lean_object* v_res_1871_; 
v_sz_boxed_1869_ = lean_unbox_usize(v_sz_1866_);
lean_dec(v_sz_1866_);
v_i_boxed_1870_ = lean_unbox_usize(v_i_1867_);
lean_dec(v_i_1867_);
v_res_1871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(v_sz_boxed_1869_, v_i_boxed_1870_, v_bs_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(lean_object* v_bs_1872_, lean_object* v_k_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
size_t v_sz_1879_; size_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_sz_1879_ = lean_array_size(v_bs_1872_);
v___x_1880_ = ((size_t)0ULL);
v___x_1881_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__19(v_sz_1879_, v___x_1880_, v_bs_1872_);
v___x_1882_ = l_Lean_Meta_withNewBinderInfos___at___00Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12_spec__20___redArg(v___x_1881_, v_k_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
lean_dec_ref(v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg___boxed(lean_object* v_bs_1883_, lean_object* v_k_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(v_bs_1883_, v_k_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_);
lean_dec(v___y_1888_);
lean_dec_ref(v___y_1887_);
lean_dec(v___y_1886_);
lean_dec_ref(v___y_1885_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2(lean_object* v_numParams_1894_, lean_object* v_indName_1895_, lean_object* v___x_1896_, lean_object* v___x_1897_, uint8_t v___x_1898_, uint8_t v___x_1899_, lean_object* v_val_1900_, lean_object* v___x_1901_, lean_object* v_ctors_1902_, lean_object* v___x_1903_, lean_object* v_levelParams_1904_, lean_object* v_xs_1905_, lean_object* v_x_1906_, lean_object* v___y_1907_, lean_object* v___y_1908_, lean_object* v___y_1909_, lean_object* v___y_1910_){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___f_1924_; lean_object* v___x_1925_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_1894_);
lean_inc_ref_n(v_xs_1905_, 3);
v___x_1913_ = l_Array_toSubarray___redArg(v_xs_1905_, v___x_1912_, v_numParams_1894_);
v___x_1914_ = l_Subarray_copy___redArg(v___x_1913_);
v___x_1915_ = lean_array_get_size(v_xs_1905_);
v___x_1916_ = l_Array_toSubarray___redArg(v_xs_1905_, v_numParams_1894_, v___x_1915_);
v___x_1917_ = l_Subarray_copy___redArg(v___x_1916_);
lean_inc(v___x_1896_);
lean_inc(v_indName_1895_);
v___x_1918_ = l_Lean_mkConst(v_indName_1895_, v___x_1896_);
v___x_1919_ = l_Lean_mkAppN(v___x_1918_, v_xs_1905_);
v___x_1920_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__2___closed__1));
v___x_1921_ = l_Lean_mkConst(v___x_1920_, v___x_1897_);
v___x_1922_ = lean_box(v___x_1898_);
v___x_1923_ = lean_box(v___x_1899_);
v___f_1924_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__1___boxed), 20, 15);
lean_closure_set(v___f_1924_, 0, v___x_1919_);
lean_closure_set(v___f_1924_, 1, v___x_1921_);
lean_closure_set(v___f_1924_, 2, v_xs_1905_);
lean_closure_set(v___f_1924_, 3, v___x_1922_);
lean_closure_set(v___f_1924_, 4, v___x_1923_);
lean_closure_set(v___f_1924_, 5, v_val_1900_);
lean_closure_set(v___f_1924_, 6, v___x_1917_);
lean_closure_set(v___f_1924_, 7, v___x_1896_);
lean_closure_set(v___f_1924_, 8, v___x_1901_);
lean_closure_set(v___f_1924_, 9, v___x_1914_);
lean_closure_set(v___f_1924_, 10, v_ctors_1902_);
lean_closure_set(v___f_1924_, 11, v___x_1912_);
lean_closure_set(v___f_1924_, 12, v___x_1903_);
lean_closure_set(v___f_1924_, 13, v_levelParams_1904_);
lean_closure_set(v___f_1924_, 14, v_indName_1895_);
v___x_1925_ = l_Lean_Meta_withImplicitBinderInfos___at___00Lean_mkCtorIdx_spec__12___redArg(v_xs_1905_, v___f_1924_, v___y_1907_, v___y_1908_, v___y_1909_, v___y_1910_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__2___boxed(lean_object** _args){
lean_object* v_numParams_1926_ = _args[0];
lean_object* v_indName_1927_ = _args[1];
lean_object* v___x_1928_ = _args[2];
lean_object* v___x_1929_ = _args[3];
lean_object* v___x_1930_ = _args[4];
lean_object* v___x_1931_ = _args[5];
lean_object* v_val_1932_ = _args[6];
lean_object* v___x_1933_ = _args[7];
lean_object* v_ctors_1934_ = _args[8];
lean_object* v___x_1935_ = _args[9];
lean_object* v_levelParams_1936_ = _args[10];
lean_object* v_xs_1937_ = _args[11];
lean_object* v_x_1938_ = _args[12];
lean_object* v___y_1939_ = _args[13];
lean_object* v___y_1940_ = _args[14];
lean_object* v___y_1941_ = _args[15];
lean_object* v___y_1942_ = _args[16];
lean_object* v___y_1943_ = _args[17];
_start:
{
uint8_t v___x_36784__boxed_1944_; uint8_t v___x_36785__boxed_1945_; lean_object* v_res_1946_; 
v___x_36784__boxed_1944_ = lean_unbox(v___x_1930_);
v___x_36785__boxed_1945_ = lean_unbox(v___x_1931_);
v_res_1946_ = l_Lean_mkCtorIdx___lam__2(v_numParams_1926_, v_indName_1927_, v___x_1928_, v___x_1929_, v___x_36784__boxed_1944_, v___x_36785__boxed_1945_, v_val_1932_, v___x_1933_, v_ctors_1934_, v___x_1935_, v_levelParams_1936_, v_xs_1937_, v_x_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
lean_dec_ref(v_x_1938_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
if (lean_obj_tag(v_a_1947_) == 0)
{
lean_object* v___x_1949_; 
v___x_1949_ = l_List_reverse___redArg(v_a_1948_);
return v___x_1949_;
}
else
{
lean_object* v_head_1950_; lean_object* v_tail_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1960_; 
v_head_1950_ = lean_ctor_get(v_a_1947_, 0);
v_tail_1951_ = lean_ctor_get(v_a_1947_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_a_1947_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1953_ = v_a_1947_;
v_isShared_1954_ = v_isSharedCheck_1960_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_tail_1951_);
lean_inc(v_head_1950_);
lean_dec(v_a_1947_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1960_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1955_ = l_Lean_mkLevelParam(v_head_1950_);
if (v_isShared_1954_ == 0)
{
lean_ctor_set(v___x_1953_, 1, v_a_1948_);
lean_ctor_set(v___x_1953_, 0, v___x_1955_);
v___x_1957_ = v___x_1953_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1955_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_a_1948_);
v___x_1957_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
v_a_1947_ = v_tail_1951_;
v_a_1948_ = v___x_1957_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkCtorIdx___lam__3___closed__2(void){
_start:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1963_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCtorIdx_spec__4___closed__6));
v___x_1964_ = lean_unsigned_to_nat(62u);
v___x_1965_ = lean_unsigned_to_nat(50u);
v___x_1966_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__1));
v___x_1967_ = ((lean_object*)(l_Lean_mkCtorIdx___lam__3___closed__0));
v___x_1968_ = l_mkPanicMessageWithDecl(v___x_1967_, v___x_1966_, v___x_1965_, v___x_1964_, v___x_1963_);
return v___x_1968_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3(lean_object* v_indName_1969_, uint8_t v___x_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_options_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_options_1976_ = lean_ctor_get(v___y_1973_, 2);
v___x_1977_ = l___private_Lean_Meta_Constructions_CtorIdx_0__Lean_genCtorIdx;
v___x_1978_ = l_Lean_Option_get___at___00Lean_mkCtorIdx_spec__0(v_options_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_indName_1969_);
v___x_1979_ = lean_box(0);
v___x_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
return v___x_1980_;
}
else
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2067_; 
lean_inc(v_indName_1969_);
v___x_1981_ = l_Lean_mkCtorIdxName(v_indName_1969_);
lean_inc(v___x_1981_);
v___x_1982_ = l_Lean_hasConst___at___00Lean_mkCtorIdx_spec__1___redArg(v___x_1981_, v___x_1978_, v___y_1974_);
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2067_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2067_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
uint8_t v___x_1987_; 
v___x_1987_ = lean_unbox(v_a_1983_);
lean_dec(v_a_1983_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1988_; 
lean_del_object(v___x_1985_);
lean_inc(v_indName_1969_);
v___x_1988_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v_indName_1969_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_1988_) == 0)
{
lean_object* v_a_1989_; 
v_a_1989_ = lean_ctor_get(v___x_1988_, 0);
lean_inc(v_a_1989_);
lean_dec_ref_known(v___x_1988_, 1);
if (lean_obj_tag(v_a_1989_) == 5)
{
lean_object* v_val_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2052_; 
v_val_1990_ = lean_ctor_get(v_a_1989_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_a_1989_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_1992_ = v_a_1989_;
v_isShared_1993_ = v_isSharedCheck_2052_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_val_1990_);
lean_dec(v_a_1989_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2052_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v_toConstantVal_1994_; lean_object* v_numParams_1995_; lean_object* v_numIndices_1996_; lean_object* v_ctors_1997_; lean_object* v_levelParams_1998_; lean_object* v_type_1999_; lean_object* v___x_2000_; 
v_toConstantVal_1994_ = lean_ctor_get(v_val_1990_, 0);
v_numParams_1995_ = lean_ctor_get(v_val_1990_, 1);
lean_inc(v_numParams_1995_);
v_numIndices_1996_ = lean_ctor_get(v_val_1990_, 2);
lean_inc(v_numIndices_1996_);
v_ctors_1997_ = lean_ctor_get(v_val_1990_, 4);
lean_inc(v_ctors_1997_);
v_levelParams_1998_ = lean_ctor_get(v_toConstantVal_1994_, 1);
lean_inc(v_levelParams_1998_);
v_type_1999_ = lean_ctor_get(v_toConstantVal_1994_, 2);
lean_inc_ref_n(v_type_1999_, 2);
v___x_2000_ = l_Lean_Meta_isPropFormerType(v_type_1999_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2043_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2043_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2043_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_unbox(v_a_2001_);
lean_dec(v_a_2001_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
lean_del_object(v___x_2003_);
lean_inc(v_indName_1969_);
v___x_2006_ = l_Lean_mkCasesOnName(v_indName_1969_);
lean_inc(v___x_2006_);
v___x_2007_ = l_Lean_getConstInfo___at___00Lean_mkCtorIdx_spec__2(v___x_2006_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2030_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2010_ = v___x_2007_;
v_isShared_2011_ = v_isSharedCheck_2030_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2030_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2012_ = l_List_lengthTR___redArg(v_levelParams_1998_);
v___x_2013_ = l_Lean_ConstantInfo_levelParams(v_a_2008_);
lean_dec(v_a_2008_);
v___x_2014_ = l_List_lengthTR___redArg(v___x_2013_);
lean_dec(v___x_2013_);
v___x_2015_ = lean_nat_dec_lt(v___x_2012_, v___x_2014_);
lean_dec(v___x_2014_);
lean_dec(v___x_2012_);
if (v___x_2015_ == 0)
{
lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_dec(v___x_2006_);
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_ctors_1997_);
lean_dec(v_numIndices_1996_);
lean_dec(v_numParams_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_val_1990_);
lean_dec(v___x_1981_);
lean_dec(v_indName_1969_);
v___x_2016_ = lean_box(0);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2016_);
v___x_2018_ = v___x_2010_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_del_object(v___x_2010_);
v___x_2020_ = lean_box(0);
lean_inc(v_levelParams_1998_);
v___x_2021_ = l_List_mapTR_loop___at___00Lean_mkCtorIdx_spec__3(v_levelParams_1998_, v___x_2020_);
v___x_2022_ = lean_box(v___x_1970_);
v___x_2023_ = lean_box(v___x_1978_);
lean_inc(v_numParams_1995_);
v___f_2024_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__2___boxed), 18, 11);
lean_closure_set(v___f_2024_, 0, v_numParams_1995_);
lean_closure_set(v___f_2024_, 1, v_indName_1969_);
lean_closure_set(v___f_2024_, 2, v___x_2021_);
lean_closure_set(v___f_2024_, 3, v___x_2020_);
lean_closure_set(v___f_2024_, 4, v___x_2022_);
lean_closure_set(v___f_2024_, 5, v___x_2023_);
lean_closure_set(v___f_2024_, 6, v_val_1990_);
lean_closure_set(v___f_2024_, 7, v___x_2006_);
lean_closure_set(v___f_2024_, 8, v_ctors_1997_);
lean_closure_set(v___f_2024_, 9, v___x_1981_);
lean_closure_set(v___f_2024_, 10, v_levelParams_1998_);
v___x_2025_ = lean_nat_add(v_numParams_1995_, v_numIndices_1996_);
lean_dec(v_numIndices_1996_);
lean_dec(v_numParams_1995_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set_tag(v___x_1992_, 1);
lean_ctor_set(v___x_1992_, 0, v___x_2025_);
v___x_2027_ = v___x_1992_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCtorIdx_spec__5___redArg(v_type_1999_, v___x_2027_, v___f_2024_, v___x_1970_, v___x_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_2028_;
}
}
}
}
else
{
lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2038_; 
lean_dec(v___x_2006_);
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_ctors_1997_);
lean_dec(v_numIndices_1996_);
lean_dec(v_numParams_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_val_1990_);
lean_dec(v___x_1981_);
lean_dec(v_indName_1969_);
v_a_2031_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2033_ = v___x_2007_;
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_dec(v___x_2007_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2038_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2036_; 
if (v_isShared_2034_ == 0)
{
v___x_2036_ = v___x_2033_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
v___x_2036_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
return v___x_2036_;
}
}
}
}
else
{
lean_object* v___x_2039_; lean_object* v___x_2041_; 
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_ctors_1997_);
lean_dec(v_numIndices_1996_);
lean_dec(v_numParams_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_val_1990_);
lean_dec(v___x_1981_);
lean_dec(v_indName_1969_);
v___x_2039_ = lean_box(0);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2039_);
v___x_2041_ = v___x_2003_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref(v_type_1999_);
lean_dec(v_levelParams_1998_);
lean_dec(v_ctors_1997_);
lean_dec(v_numIndices_1996_);
lean_dec(v_numParams_1995_);
lean_del_object(v___x_1992_);
lean_dec_ref(v_val_1990_);
lean_dec(v___x_1981_);
lean_dec(v_indName_1969_);
v_a_2044_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2000_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_dec(v___x_2000_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
else
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
lean_dec(v_a_1989_);
lean_dec(v___x_1981_);
lean_dec(v_indName_1969_);
v___x_2053_ = lean_obj_once(&l_Lean_mkCtorIdx___lam__3___closed__2, &l_Lean_mkCtorIdx___lam__3___closed__2_once, _init_l_Lean_mkCtorIdx___lam__3___closed__2);
v___x_2054_ = l_panic___at___00Lean_mkCtorIdx_spec__13(v___x_2053_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
return v___x_2054_;
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v___x_1981_);
lean_dec(v_indName_1969_);
v_a_2055_ = lean_ctor_get(v___x_1988_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_1988_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_1988_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_1988_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
lean_dec(v___x_1981_);
lean_dec(v_indName_1969_);
v___x_2063_ = lean_box(0);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_2063_);
v___x_2065_ = v___x_1985_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__3___boxed(lean_object* v_indName_2068_, lean_object* v___x_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
uint8_t v___x_36897__boxed_2075_; lean_object* v_res_2076_; 
v___x_36897__boxed_2075_ = lean_unbox(v___x_2069_);
v_res_2076_ = l_Lean_mkCtorIdx___lam__3(v_indName_2068_, v___x_36897__boxed_2075_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__4(lean_object* v___x_2077_, lean_object* v_e_2078_){
_start:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = l_Lean_indentD(v_e_2078_);
v___x_2080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2077_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5(lean_object* v___f_2081_, lean_object* v___f_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_mapErrorImp___redArg(v___f_2081_, v___f_2082_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2096_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2096_ == 0)
{
v___x_2091_ = v___x_2088_;
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_a_2089_);
lean_dec(v___x_2088_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2096_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2094_; 
if (v_isShared_2092_ == 0)
{
v___x_2094_ = v___x_2091_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v_a_2089_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
}
else
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2104_; 
v_a_2097_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2099_ = v___x_2088_;
v_isShared_2100_ = v_isSharedCheck_2104_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2088_);
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
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx___lam__5___boxed(lean_object* v___f_2105_, lean_object* v___f_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_mkCtorIdx___lam__5(v___f_2105_, v___f_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
return v_res_2112_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__1(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__0));
v___x_2115_ = l_Lean_stringToMessageData(v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_mkCtorIdx___closed__3(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l_Lean_mkCtorIdx___closed__2));
v___x_2118_ = l_Lean_stringToMessageData(v___x_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCtorIdx(lean_object* v_indName_2119_, lean_object* v_a_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v___x_2125_; uint8_t v___x_2126_; lean_object* v___x_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___f_2134_; uint8_t v___x_2135_; 
v___x_2125_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__1, &l_Lean_mkCtorIdx___closed__1_once, _init_l_Lean_mkCtorIdx___closed__1);
v___x_2126_ = 0;
v___x_2127_ = lean_box(v___x_2126_);
lean_inc_n(v_indName_2119_, 2);
v___f_2128_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__3___boxed), 7, 2);
lean_closure_set(v___f_2128_, 0, v_indName_2119_);
lean_closure_set(v___f_2128_, 1, v___x_2127_);
v___x_2129_ = l_Lean_MessageData_ofConstName(v_indName_2119_, v___x_2126_);
v___x_2130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2125_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = lean_obj_once(&l_Lean_mkCtorIdx___closed__3, &l_Lean_mkCtorIdx___closed__3_once, _init_l_Lean_mkCtorIdx___closed__3);
v___x_2132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2130_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___f_2133_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__4), 2, 1);
lean_closure_set(v___f_2133_, 0, v___x_2132_);
v___f_2134_ = lean_alloc_closure((void*)(l_Lean_mkCtorIdx___lam__5___boxed), 7, 2);
lean_closure_set(v___f_2134_, 0, v___f_2128_);
lean_closure_set(v___f_2134_, 1, v___f_2133_);
v___x_2135_ = l_Lean_isPrivateName(v_indName_2119_);
lean_dec(v_indName_2119_);
if (v___x_2135_ == 0)
{
uint8_t v___x_2136_; lean_object* v___x_2137_; 
v___x_2136_ = 1;
v___x_2137_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v___f_2134_, v___x_2136_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_withExporting___at___00Lean_mkCtorIdx_spec__14___redArg(v___f_2134_, v___x_2126_, v_a_2120_, v_a_2121_, v_a_2122_, v_a_2123_);
return v___x_2138_;
}
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
uint8_t v___x_37204__boxed_2169_; lean_object* v_res_2170_; 
v___x_37204__boxed_2169_ = lean_unbox(v___x_2158_);
v_res_2170_ = l_List_forIn_x27_loop___at___00Lean_mkCtorIdx_spec__6(v___x_37204__boxed_2169_, v___x_2159_, v_as_2160_, v_as_x27_2161_, v_b_2162_, v_a_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
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
